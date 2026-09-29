import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell166.Parameters
import ForestUnimodality.BinomialMassData.Q113_213.Batch000_049
import ForestUnimodality.BinomialMassData.Q113_213.Batch050_099
import ForestUnimodality.BinomialMassData.Q8069_15194.Batch000_049
import ForestUnimodality.BinomialMassData.Q8069_15194.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree000.table
  base := (14499052409709763507628111/312500000000000000000000)
  polynomial :=
    { denominator := 2130000000000000000000000000000000000000000
      center := (11413)
      previous := (0)
      next := (10100)
      square := (429840957857115048557083972800000000000000)
      linear := (-1744639117561141097301202755900000000000000)
      constant := (98825541224581748067993204576000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree000.table
  base := (14499052409709763507628111/312500000000000000000000)
  polynomial :=
    { denominator := 151940000000000000000000000000000000000000000
      center := (814969)
      previous := (0)
      next := (719625)
      square := (30661988327140873463738656726400000000000000)
      linear := (-124450923719361398274152463254200000000000000)
      constant := (7049555274020164695516848593088000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree001.table
  base := (13334738047041700225873250064182224067111/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-468752188516231054699057164859500000000000000)
      constant := (12322587088521207843563048302300766474015179180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree001.table
  base := (66623075633827781916944537648120874185759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-1192865251307688250667643484467479000000000000000)
      constant := (31328684542765388449538722955077800413555495211448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (2495170196391733673/5000000000000000000)
  directionHi := (49903403927834673461/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree002.table
  base := (162388072890755208190874722940152731438733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-565896244991939055672958142712300000000000000)
      constant := (7864745955997894722862438118490789272643877477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree002.table
  base := (162175351342893991937135511408792307793631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-1440276835119387958646550705592800600000000000000)
      constant := (19986686830817525948330923545589993896111014258158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2495170196391733673/5000000000000000000)
  centralHi := (49903403927834673461/100000000000000000000)
  directionLo := (2822962825733063097/4000000000000000000)
  directionHi := (35287035321663288713/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree003.table
  base := (2102811886150298365789857767812483128189/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-221013433822549018882286373521700000000000000)
      constant := (1864490205333259899132465105487309117380112350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree003.table
  base := (52483635185027903533894727694282988642017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-1687688418931087666625457926718122200000000000000)
      constant := (14213801932171578521248523144024358372910894891812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2822962825733063097/4000000000000000000)
  centralHi := (35287035321663288713/50000000000000000000)
  directionLo := (43217615536820964647/50000000000000000000)
  directionHi := (17287046214728385859/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree004.table
  base := (72036074509098075633002416188771506170623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-760184357943355057620760098417900000000000000)
      constant := (4469073691334521547216114228077574463454994887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree004.table
  base := (71904506451945714670937134457086056769337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-1935100002742787374604365147843443800000000000000)
      constant := (11359374047928652438186624562082567657165468553666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43217615536820964647/50000000000000000000)
  centralHi := (17287046214728385859/20000000000000000000)
  directionLo := (2495170196391733673/2500000000000000000)
  directionHi := (99806807855669346921/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree005.table
  base := (3224129358089346529333668355312097287801/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-857328414419063058594661076270700000000000000)
      constant := (3970335976779057438383175442037972669603897104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree005.table
  base := (3217914876201155910559590580267087985563/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-2182511586554487082583272368968765400000000000000)
      constant := (10095923109837523900092212536960994947608610472544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2495170196391733673/2500000000000000000)
  centralHi := (99806807855669346921/100000000000000000000)
  directionLo := (55793701745634169687/50000000000000000000)
  directionHi := (178539845586029343/160000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree006.table
  base := (18994951794791679676999482156627619627463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-318157490298257019856187351374500000000000000)
      constant := (1278028861899298414882311131899558983252245898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree006.table
  base := (3791265562217932540062903050161607625669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-2429923170366186790562179590094087000000000000000)
      constant := (9753845453913089216519738511926898972107591292420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55793701745634169687/50000000000000000000)
  centralHi := (178539845586029343/160000000000000000)
  directionLo := (24447575210239358779/20000000000000000000)
  directionHi := (15279734506399599237/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree007.table
  base := (28284210983271193842722171419901079362239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-1051616527370479060542463031976300000000000000)
      constant := (3925880606583839883557708209739992069585421191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree007.table
  base := (28221745131455698893831488825169035090481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-2677334754177886498541086811219408600000000000000)
      constant := (9991377804884180675921738452418638870694744881458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24447575210239358779/20000000000000000000)
  centralHi := (15279734506399599237/12500000000000000000)
  directionLo := (132031996368654427027/100000000000000000000)
  directionHi := (33007999092163606757/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree008.table
  base := (4185322696946442138994524543376027077961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-1148760583846187061516364009829100000000000000)
      constant := (4175741872638547930349636060745334862500063045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree008.table
  base := (20874092431785481592900035551546693781167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-2924746337989586206519994032344730200000000000000)
      constant := (10630781239486374453353032109456663334968057470606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132031996368654427027/100000000000000000000)
  centralHi := (33007999092163606757/25000000000000000000)
  directionLo := (2822962825733063097/2000000000000000000)
  directionHi := (141148141286653154851/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree009.table
  base := (15091040105917381246251578395606354235681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-415301546773965020830088329227300000000000000)
      constant := (1515397456401741001181024540779654895106203763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree009.table
  base := (3009101509658343198671264613156895375711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-3172157921801285914498901253470051800000000000000)
      constant := (11576920483112173648635454111252492308839933197990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2822962825733063097/2000000000000000000)
  centralHi := (141148141286653154851/100000000000000000000)
  directionLo := (149710211783504020381/100000000000000000000)
  directionHi := (74855105891752010191/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree010.table
  base := (10316377600161247197709567237017245393681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-1343048696797603063464165965534700000000000000)
      constant := (5016311849395899925577519234783235406265913289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree010.table
  base := (2569021761536080761728260386001954791259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-3419569505612985622477808474595373400000000000000)
      constant := (12776709425885002206378635360436496548977852407448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149710211783504020381/100000000000000000000)
  centralHi := (74855105891752010191/50000000000000000000)
  directionLo := (252493471051760867/160000000000000000)
  directionHi := (39452104851837635469/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree011.table
  base := (6330665284091835303522352943188514208579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-1440192753273311064438066943387500000000000000)
      constant := (5573761728966675642263173121477619701129020651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree011.table
  base := (6294589887325516577962707205710401133181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-3666981089424685330456715695720695000000000000000)
      constant := (14198839035393374005355463572270660153108943410058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252493471051760867/160000000000000000)
  centralHi := (39452104851837635469/25000000000000000000)
  directionLo := (82755433295087755623/50000000000000000000)
  directionHi := (165510866590175511247/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree012.table
  base := (1481302491710939157902860417000947242639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-512445603249673021803989307080100000000000000)
      constant := (2070256793682770375276925448866610650300859194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree012.table
  base := (293012217971927304450681662270374140119/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-3914392673236385038435622916846016600000000000000)
      constant := (15823583231666916929252878138270238834117025493420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82755433295087755623/50000000000000000000)
  centralHi := (165510866590175511247/100000000000000000000)
  directionLo := (43217615536820964647/25000000000000000000)
  directionHi := (172870462147283858589/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree013.table
  base := (48292375846157698389990151021653316723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-1634480866224727066385868899093100000000000000)
      constant := (6922092607241905245131102126982102778652811574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree013.table
  base := (33644180478573756157715533541362117353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-4161804257048084746414530137971338200000000000000)
      constant := (17637622041338996098814629490860721466632068157508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43217615536820964647/25000000000000000000)
  centralHi := (172870462147283858589/100000000000000000000)
  directionLo := (179929281681998959997/100000000000000000000)
  directionHi := (89964640840999479999/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree014.table
  base := (-470108410351665575063731150367187274497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-1731624922700435067359769876945900000000000000)
      constant := (7703956127607287567123149205723155402716728035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree014.table
  base := (-1188473686895607947261361877987147290833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-4409215840859784454393437359096659800000000000000)
      constant := (19631370739606364844764924565317062138054489149212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179929281681998959997/100000000000000000000)
  centralHi := (89964640840999479999/50000000000000000000)
  directionLo := (186721439931746326521/100000000000000000000)
  directionHi := (93360719965873163261/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree015.table
  base := (-1110435512409507345954046482147943925249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-609589659725381022777890284932900000000000000)
      constant := (2851168069812939947739433450765406576073837492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree015.table
  base := (-2232748437997069696159558840481465136971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-4656627424671484162372344580221981400000000000000)
      constant := (21797567485815843169231790078800776356662458739444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186721439931746326521/100000000000000000000)
  centralHi := (93360719965873163261/50000000000000000000)
  directionLo := (48318763082891371189/25000000000000000000)
  directionHi := (193275052331565484757/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree016.table
  base := (-1245308236489905626578524919625885048863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-1925913035651851069307571832651500000000000000)
      constant := (9468489910341833307535912494753066106090672765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree016.table
  base := (-1249571841973056825716593325997211867059/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-4904039008483183870351251801347303000000000000000)
      constant := (24130498661493142066505713593316749014449032468690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48318763082891371189/25000000000000000000)
  centralHi := (193275052331565484757/100000000000000000000)
  directionLo := (199613615711338693841/100000000000000000000)
  directionHi := (99806807855669346921/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree017.table
  base := (-30979643063496576989926656284644989129/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-2023057092127559070281472810504300000000000000)
      constant := (10447099771695182147327868946648985372051599750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree017.table
  base := (-1940997862060052571344377567807313708149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-5151450592294883578330159022472624600000000000000)
      constant := (26625552068950112916403270552715607207652655848472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199613615711338693841/100000000000000000000)
  centralHi := (99806807855669346921/50000000000000000000)
  directionLo := (102878502736162800061/50000000000000000000)
  directionHi := (205757005472325600123/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree018.table
  base := (-9029652128102279130094470943258467451469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-706733716201089023751791262785700000000000000)
      constant := (3829281876680065347121213530236502196731434313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree018.table
  base := (-9046685491539278366868988846615442971133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-5398862176106583286309066243597946200000000000000)
      constant := (29278942577881259802794667770368153517295709689206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102878502736162800061/50000000000000000000)
  centralHi := (205757005472325600123/100000000000000000000)
  directionLo := (52930552982494933069/25000000000000000000)
  directionHi := (211722211929979732277/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree019.table
  base := (-5053982021685248903811188424823804448283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-2217345205078975072229274766209900000000000000)
      constant := (12589493504188536270938194601976037631971697146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree019.table
  base := (-10123131797822191458486436779683909728087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-5646273759918282994287973464723267800000000000000)
      constant := (32087531625851872625097878779883936786468216188834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52930552982494933069/25000000000000000000)
  centralHi := (211722211929979732277/100000000000000000000)
  directionLo := (27190486832515257137/12500000000000000000)
  directionHi := (217523894660122057097/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree020.table
  base := (-11002543847229302124692032791310699813679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-2314489261554683073203175744062700000000000000)
      constant := (13751013638723612117862664451185024860153197449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree020.table
  base := (-688501185762500821159818450336164145157/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-5893685343729982702266880685848589400000000000000)
      constant := (35048700293991912555743739719855395921128753049184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27190486832515257137/12500000000000000000)
  centralHi := (217523894660122057097/100000000000000000000)
  directionLo := (55793701745634169687/25000000000000000000)
  directionHi := (223174806982536678749/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree021.table
  base := (-11732405955481888500927927674400177107029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-803877772676797024725692240638500000000000000)
      constant := (4990514456204949454591702233717746121610400433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree021.table
  base := (-11744351850426967426173455268322447841501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-6141096927541682410245787906973911000000000000000)
      constant := (38160254876573985377701194904783247702788888224182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55793701745634169687/25000000000000000000)
  centralHi := (223174806982536678749/100000000000000000000)
  directionLo := (228686125935258974589/100000000000000000000)
  directionHi := (22868612593525897459/10000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree022.table
  base := (-12313517056257476772396154868690429362091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-2508777374506099075150977699768300000000000000)
      constant := (16250358301188510433933038761787383910271293421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree022.table
  base := (-12324086756921559894946124640452982052981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-6388508511353382118224695128099232600000000000000)
      constant := (41420353553930838455281959898834002297049189793542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228686125935258974589/100000000000000000000)
  centralHi := (22868612593525897459/10000000000000000000)
  directionLo := (234067712251950188813/100000000000000000000)
  directionHi := (117033856125975094407/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree023.table
  base := (-12759304062120675139578294500731199873597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-2605921430981807076124878677621100000000000000)
      constant := (17586849270848454618888811824326026192934777707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree023.table
  base := (-3192159929273954174570479693291804598907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-6635920095165081826203602349224554200000000000000)
      constant := (44827447730106903646613199321308768764244803592296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234067712251950188813/100000000000000000000)
  centralHi := (117033856125975094407/50000000000000000000)
  directionLo := (119664158838858656857/50000000000000000000)
  directionHi := (47865663535543462743/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree024.table
  base := (-2616213680477809731654966233031353965959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-901021829152505025699593218491300000000000000)
      constant := (6326834514349324103208604567731734169864010215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree024.table
  base := (-13089301052514792272773494293570275573301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-6883331678976781534182509570349875800000000000000)
      constant := (48380234176629086807973366870260936490639593211782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119664158838858656857/50000000000000000000)
  centralHi := (47865663535543462743/20000000000000000000)
  directionLo := (24447575210239358779/10000000000000000000)
  directionHi := (244475752102393587791/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree025.table
  base := (-6644164078697053520211449975882018344387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-2800209543933223078072680633326700000000000000)
      constant := (20430889292000503242023168516505917419467012394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree025.table
  base := (-6647788896009166740414278384434353662389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-7130743262788481242161416791475197400000000000000)
      constant := (52077615508395712504733732457975833416312933347596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24447575210239358779/10000000000000000000)
  centralHi := (244475752102393587791/100000000000000000000)
  directionLo := (124758509819586683651/50000000000000000000)
  directionHi := (249517019639173367303/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree026.table
  base := (-669455138795675299068446472644676133437/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-2897353600408931079046581611179500000000000000)
      constant := (21937642683334453954838704145452273770041934940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree026.table
  base := (-13395478614257717212828319493494110428841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-7378154846600180950140324012600519000000000000000)
      constant := (55918667293096322011246877064471334343237410260062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124758509819586683651/50000000000000000000)
  centralHi := (249517019639173367303/100000000000000000000)
  directionLo := (63614607605682956157/25000000000000000000)
  directionHi := (254458430422731824629/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree027.table
  base := (-13390151116520070241554172498695673184023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-998165885628213026673494196344100000000000000)
      constant := (7833485691465077987171987130127725334438020171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree027.table
  base := (-13395752057607078512392010695632730503983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-7625566430411880658119231233725840600000000000000)
      constant := (59902610554923161277655454733295666655812698017906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63614607605682956157/25000000000000000000)
  centralHi := (254458430422731824629/100000000000000000000)
  directionLo := (129652846610462893941/50000000000000000000)
  directionHi := (259305693220925787883/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree028.table
  base := (-415536594529717921004822021124140276147/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-3091641713360347080994383566885100000000000000)
      constant := (25119073959619593430674751025601004153967576224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree028.table
  base := (-831380388387571185638852494302340494931/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-7872978014223580366098138454851162200000000000000)
      constant := (64028788724124444293985652713766090032585274855072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129652846610462893941/50000000000000000000)
  centralHi := (259305693220925787883/100000000000000000000)
  directionLo := (132031996368654427027/50000000000000000000)
  directionHi := (52812798547461770811/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree029.table
  base := (-6557483473748282871418232391859929115079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-3188785769836055081968284544737900000000000000)
      constant := (26793275366083785470004344630934113751955961698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree029.table
  base := (-6559638208131312033386879122498545379357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-8120389598035280074077045675976483800000000000000)
      constant := (68296648281169784545289889210680691300282919779948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132031996368654427027/50000000000000000000)
  centralHi := (52812798547461770811/20000000000000000000)
  directionLo := (53747610917678612047/20000000000000000000)
  directionHi := (67184513647098265059/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree030.table
  base := (-12847590846057598083115022618820689022549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-1095309942103921027647395174196900000000000000)
      constant := (9507625820109444968682234921022574719911991473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree030.table
  base := (-2570273237831746441910670968639359495393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-8367801181846979782055952897101805400000000000000)
      constant := (72705722486705493303418380998612035325848547822630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53747610917678612047/20000000000000000000)
  centralHi := (67184513647098265059/25000000000000000000)
  directionLo := (54666440055133918863/20000000000000000000)
  directionHi := (68333050068917398579/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree031.table
  base := (-2499692148863609133138470927014999834421/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-3383073882787471083916086500443500000000000000)
      constant := (30307725170036723469191497304669382362560768255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree031.table
  base := (-2500353161750613019924609292204890064501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-8615212765658679490034860118227127000000000000000)
      constant := (77255617696619581094794680881244760330173529050910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54666440055133918863/20000000000000000000)
  centralHi := (68333050068917398579/25000000000000000000)
  directionLo := (277850393973309633969/100000000000000000000)
  directionHi := (27785039397330963397/10000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree032.table
  base := (-3017615124404670255067532899851591937947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-3480217939263179084889987478296300000000000000)
      constant := (32147687657575995650538687154714532501469130228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree032.table
  base := (-368449464800989904956659679842341903/305175781250000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-8862624349470379198013767339352448600000000000000)
      constant := (81946001846725143261203522882829328285813615689728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277850393973309633969/100000000000000000000)
  centralHi := (27785039397330963397/10000000000000000000)
  directionLo := (282296282573306309701/100000000000000000000)
  directionHi := (141148141286653154851/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree033.table
  base := (-5783011892202647767479624029065375888669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-1192453998579629028621296152049700000000000000)
      constant := (11347551503129581446867023712843788640871317426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree033.table
  base := (-723034513659848985681138641667980141059/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-9110035933282078905992674560477770200000000000000)
      constant := (86776594760361953401839151292150449961921381787808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282296282573306309701/100000000000000000000)
  centralHi := (141148141286653154851/50000000000000000000)
  directionLo := (286673230138938206361/100000000000000000000)
  directionHi := (143336615069469103181/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree034.table
  base := (-2746801207330274159848820700576310318177/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-3674506052214595086837789434001900000000000000)
      constant := (35992532527357131861503512681948413508698510748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree034.table
  base := (-2197882943091866960098227132482140528741/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-9357447517093778613971581781603091800000000000000)
      constant := (91747159988657115850316083537467746963287656709310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286673230138938206361/100000000000000000000)
  centralHi := (143336615069469103181/50000000000000000000)
  directionLo := (290984347692237999371/100000000000000000000)
  directionHi := (72746086923059499843/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree035.table
  base := (-2583934490962446815729336895345807427757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-3771650108690303087811690411854700000000000000)
      constant := (37997243026596074095044825624004724251240370668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree035.table
  base := (-1292208585655967554810976234686533054913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-9604859100905478321950489002728413400000000000000)
      constant := (96857497939954209027896569732291769611627706537328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290984347692237999371/100000000000000000000)
  centralHi := (72746086923059499843/25000000000000000000)
  directionLo := (59046503817063336447/20000000000000000000)
  directionHi := (73808129771329170559/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree036.table
  base := (-9613087793489660813146763053891186858917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-1289598055055337029595197129902500000000000000)
      constant := (13352239853139572989204879422581203581132598209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree036.table
  base := (-9614774078286589150713032033098735138919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-9852270684717178029929396223853735000000000000000)
      constant := (102107440093908402161968420842409389325619514032258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59046503817063336447/20000000000000000000)
  centralHi := (73808129771329170559/25000000000000000000)
  directionLo := (149710211783504020381/50000000000000000000)
  directionHi := (299420423567008040763/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree037.table
  base := (-176409829170434624492833715430475047841/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-3965938221641719089759492367560300000000000000)
      constant := (42170905998007657158015981608571238877725083550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree037.table
  base := (-1764392776180868608215665591787416566369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-10099682268528877737908303444979056600000000000000)
      constant := (107496844128365190712119336264721061492352038890790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149710211783504020381/50000000000000000000)
  centralHi := (299420423567008040763/100000000000000000000)
  directionLo := (303550555546569753359/100000000000000000000)
  directionHi := (3794381944332121917/1250000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree038.table
  base := (-7958994239020451020791465259067713101283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-4063082278117427090733393345413100000000000000)
      constant := (44339754919051190829715204247897556924307891573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree038.table
  base := (-248758739915468778480482768208433415081/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-10347093852340577445887210666104378200000000000000)
      constant := (113025589814492213913965077907496293104495897463744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303550555546569753359/100000000000000000000)
  centralHi := (3794381944332121917/1250000000000000000)
  directionLo := (153812620984280540907/50000000000000000000)
  directionHi := (61525048393712216363/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree039.table
  base := (-7029479556235017455485444142717859123041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-1386742111531045030569098107755300000000000000)
      constant := (15521075414203555050833533533371577816482250957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree039.table
  base := (-1406120321789186828348067234259911109369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-10594505436152277153866117887229699800000000000000)
      constant := (118693575558597911727169525275538749679302338020790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153812620984280540907/50000000000000000000)
  centralHi := (61525048393712216363/20000000000000000000)
  directionLo := (155823328821297149413/50000000000000000000)
  directionHi := (311646657642594298827/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree040.table
  base := (-241307770225385551905484829397121507191/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-4257370391068843092681195301118700000000000000)
      constant := (48841286085053987616419834160285049858506288025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree040.table
  base := (-1206734723519505002448208176285940019783/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-10841917019963976861845025108355021400000000000000)
      constant := (124500715488366530962276278379706967567487758467530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155823328821297149413/50000000000000000000)
  centralHi := (311646657642594298827/100000000000000000000)
  directionLo := (252493471051760867/80000000000000000)
  directionHi := (315616838814701083751/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree041.table
  base := (-621158739579519299428250084133980774369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-4354514447544551093655096278971500000000000000)
      constant := (51173905792254595637085348937146503409981222712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree041.table
  base := (-2485062358605410318252251925528851908719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-11089328603775676569823932329480343000000000000000)
      constant := (130446936997460042452917067711486331898559043871716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252493471051760867/80000000000000000)
  centralHi := (315616838814701083751/100000000000000000000)
  directionLo := (63907539044143963881/20000000000000000000)
  directionHi := (159768847610359909703/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree042.table
  base := (-959935204013165176594645876501382466911/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-1483886168006753031542999085608100000000000000)
      constant := (17853687041535918613771875057555678371811619788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree042.table
  base := (-3840486922247984915366544101507956484051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-11336740187587376277802839550605664600000000000000)
      constant := (136532178676077919714296145469183451565450557218282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63907539044143963881/20000000000000000000)
  centralHi := (159768847610359909703/50000000000000000000)
  directionLo := (161705510412102418581/50000000000000000000)
  directionHi := (323411020824204837163/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree043.table
  base := (-2644559073053967031576362084565576469241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-4548802560495967095602898234677100000000000000)
      constant := (56002731569918853150929896617697044361167005071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree043.table
  base := (-2645210360179827154103006855490940488461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-11584151771399075985781746771730986200000000000000)
      constant := (142756388566538257898802119674789908829708604130902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161705510412102418581/50000000000000000000)
  centralHi := (323411020824204837163/100000000000000000000)
  directionLo := (327238503410186864193/100000000000000000000)
  directionHi := (163619251705093432097/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree044.table
  base := (-346026854982077368792361784920012197983/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-4645946616971675096576799212529900000000000000)
      constant := (58498899764006702582118976898485055866358837092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree044.table
  base := (-1384676012529068666853325320808300021347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-11831563355210775693760653992856307800000000000000)
      constant := (149119522692594209445000468865939211523946541022154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327238503410186864193/100000000000000000000)
  centralHi := (163619251705093432097/50000000000000000000)
  directionLo := (331021733180351022493/100000000000000000000)
  directionHi := (165510866590175511247/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree045.table
  base := (-29354986337221472856645902221088909873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-1581030224482461032516900063460900000000000000)
      constant := (20349850334017518874478871220611920944831981242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree045.table
  base := (-59206458423400317690883085369480468819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-12078974939022475401739561213981629400000000000000)
      constant := (155621543819318353525381803709818373276210136974058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331021733180351022493/100000000000000000000)
  centralHi := (165510866590175511247/50000000000000000000)
  directionLo := (167381105236902509061/50000000000000000000)
  directionHi := (334762210473805018123/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree046.table
  base := (1331358683670433548348158013654734704777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-4840234729923091098524601168235500000000000000)
      constant := (63654672826407862593068713525872101658821027713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree046.table
  base := (83182816533905851367814588353093768757/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-12326386522834175109718468435106951000000000000000)
      constant := (162262420407218102571403770485140735085932573427616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167381105236902509061/50000000000000000000)
  centralHi := (334762210473805018123/100000000000000000000)
  directionLo := (338461352719764380621/100000000000000000000)
  directionHi := (169230676359882190311/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree047.table
  base := (5571731659634381011631920004721777721/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-4937378786398799099498502146088300000000000000)
      constant := (66314254678831191974675381676829611166712024500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree047.table
  base := (2785487017126065304951234801647216848447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-12573798106645874817697375656232272600000000000000)
      constant := (169042125729992368669787580505605895193805922345646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338461352719764380621/100000000000000000000)
  centralHi := (169230676359882190311/50000000000000000000)
  directionLo := (85530125178382828527/25000000000000000000)
  directionHi := (342120500713531314109/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree048.table
  base := (4304614143850835870412187355181703868067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-1678174280958169033490801041313700000000000000)
      constant := (23009429202341527831218448284474812907596777241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree048.table
  base := (2152141554911189656648512922058248937159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-12821209690457574525676282877357594200000000000000)
      constant := (175960637130175611320042837545336458003932039296124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85530125178382828527/25000000000000000000)
  centralHi := (342120500713531314109/100000000000000000000)
  directionLo := (43217615536820964647/12500000000000000000)
  directionHi := (345740924294567717177/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree049.table
  base := (735929530208216556343005110096307640149/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-5131666899350215101446304101793900000000000000)
      constant := (71796764016938548496272303149144375050607359848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree049.table
  base := (1471786715238971567841938880692350473213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-13068621274269274233655190098482915800000000000000)
      constant := (183017935390984803198248630142888950047058869008936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43217615536820964647/12500000000000000000)
  centralHi := (345740924294567717177/100000000000000000000)
  directionLo := (349323827494842714223/100000000000000000000)
  directionHi := (21832739218427669639/6250000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree050.table
  base := (3767095033922716713845984790476455960223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-5228810955825923102420205079646700000000000000)
      constant := (74619677463660898206789621654753252660918714574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree050.table
  base := (3766968501643649559855940854134733450671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-13316032858080973941634097319608237400000000000000)
      constant := (190214004206109491275969771061996860389912029673756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349323827494842714223/100000000000000000000)
  centralHi := (21832739218427669639/6250000000000000000)
  directionLo := (352870353216632887127/100000000000000000000)
  directionHi := (44108794152079110891/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree051.table
  base := (288898593862329385753923261306130698433/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-1775318337433877034464702019166500000000000000)
      constant := (25832340824945834730868583310896143665676872288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree051.table
  base := (23111334014785136544788002315993569643/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-13563444441892673649613004540733559000000000000000)
      constant := (197548829732067351005194998965219565795796868789600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352870353216632887127/100000000000000000000)
  centralHi := (44108794152079110891/12500000000000000000)
  directionLo := (356381587491295460257/100000000000000000000)
  directionHi := (178190793745647730129/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree052.table
  base := (5509514289676080415312020151752734196993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-5423099068777339104368007035352300000000000000)
      constant := (80428794401526858327812439114063739595566750834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree052.table
  base := (5509417399629554562250744017292152830893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-13810856025704373357591911761858880600000000000000)
      constant := (205022400210173514078454297409248447523890665748948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356381587491295460257/100000000000000000000)
  centralHi := (178190793745647730129/50000000000000000000)
  directionLo := (179929281681998959997/50000000000000000000)
  directionHi := (71971712672799583999/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree053.table
  base := (12856923697414978844739530347507364550779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-5520243125253047105341908013205100000000000000)
      constant := (83414989292193258866879869196158761622304292451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree053.table
  base := (12856754008632915850245157879246106171913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-14058267609516073065570818982984202200000000000000)
      constant := (212634705647213897392911661964446956666526422388834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179929281681998959997/50000000000000000000)
  centralHi := (71971712672799583999/20000000000000000000)
  directionLo := (45412783055473683151/12500000000000000000)
  directionHi := (363302264443789465209/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree054.table
  base := (1844795785599913307623785446549120463619/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-1872462393909585035438602997019300000000000000)
      constant := (28818534595406502957438953176266698790170481096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree054.table
  base := (3689554404186235229792537094764368512679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-14305679193327772773549726204109523800000000000000)
      constant := (220385737545631670260674217188473087583739819933688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45412783055473683151/12500000000000000000)
  centralHi := (363302264443789465209/100000000000000000000)
  directionLo := (73342725630718076337/20000000000000000000)
  directionHi := (183356814076795190843/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree055.table
  base := (16723293309118844376234327913470859509061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-5714531238204463107289709968910700000000000000)
      constant := (89550635023889274331039161981384759425066588509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree055.table
  base := (16723162988077769153533200455928997324391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-14553090777139472481528633425234845400000000000000)
      constant := (228275488675483092629359798778475209753079615699838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73342725630718076337/20000000000000000000)
  centralHi := (183356814076795190843/50000000000000000000)
  directionLo := (185046774355265634637/50000000000000000000)
  directionHi := (14803741948421250771/4000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree056.table
  base := (4687912775205255100719946567650621363621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-5811675294680171108263610946763500000000000000)
      constant := (92700080570268624595467920681756564162584484596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree056.table
  base := (73248190619500072138091846851582158401/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-14800502360951172189507540646360167000000000000000)
      constant := (236303952881637327639333037610235261593373747204608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185046774355265634637/50000000000000000000)
  centralHi := (14803741948421250771/4000000000000000000)
  directionLo := (373442879863492653043/100000000000000000000)
  directionHi := (93360719965873163261/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree057.table
  base := (10421696967011675280817708461408414950063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-1969606450385293036412503974872100000000000000)
      constant := (31967979450273332416648890428092258918579605498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree057.table
  base := (1302705851444871310610715795468361284563/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-15047913944762871897486447867485488600000000000000)
      constant := (244471124920720723842194705854134706691585099784544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373442879863492653043/100000000000000000000)
  centralHi := (93360719965873163261/25000000000000000000)
  directionLo := (376762437411591804183/100000000000000000000)
  directionHi := (47095304676448975523/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree058.table
  base := (4599696565137236641018642735611736016419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-6005963407631587110211412902469100000000000000)
      constant := (99162206596921866338884159956018044256644568055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree058.table
  base := (11499197370136952524768261047635401554391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-15295325528574571605465355088610810200000000000000)
      constant := (252777000323169968174146030432615777592757431679676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376762437411591804183/100000000000000000000)
  centralHi := (47095304676448975523/12500000000000000000)
  directionLo := (190026500762333315581/50000000000000000000)
  directionHi := (380053001524666631163/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree059.table
  base := (3152110564896438290111749879839730989739/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-6103107464107295111185313880321900000000000000)
      constant := (102474883799753821895291663173091290042187749528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree059.table
  base := (315210089013189549891201622108634485807/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-15542737112386271313444262309736131800000000000000)
      constant := (261221575276486083005444710156097656603259182890080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190026500762333315581/50000000000000000000)
  centralHi := (380053001524666631163/100000000000000000000)
  directionLo := (19165765944222845081/5000000000000000000)
  directionHi := (383315318884456901621/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree060.table
  base := (13749285311778042170653590629560254671311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-2066750506861001037386404952724900000000000000)
      constant := (35280656223749355881565603906195679462788472506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree060.table
  base := (27498502572545396754833689862521173481457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-15790148696197971021423169530861453400000000000000)
      constant := (269804846526394061425510014051852475554937526427826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19165765944222845081/5000000000000000000)
  centralHi := (383315318884456901621/100000000000000000000)
  directionLo := (48318763082891371189/12500000000000000000)
  directionHi := (386550104663130969513/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree061.table
  base := (3730439610568536569251284220646134198237/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-6297395577058711113133115836027500000000000000)
      constant := (109263460111011646865526246699125055699518515624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree061.table
  base := (5968691402535153580797757395484457172703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-16037560280009670729402076751986775000000000000000)
      constant := (278526811293129162765309430911945447844083645775270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48318763082891371189/12500000000000000000)
  centralHi := (386550104663130969513/100000000000000000000)
  directionLo := (389758044354009622301/100000000000000000000)
  directionHi := (194879022177004811151/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree062.table
  base := (8062925641658492493905788730203815415197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-6394539633534419114107016813880300000000000000)
      constant := (112739357178295017588124995376199467606288290772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree062.table
  base := (322516498557240596733141952711726083801/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-16284971863821370437380983973112096600000000000000)
      constant := (287387467200505803751838786216029892659291837721800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389758044354009622301/100000000000000000000)
  centralHi := (194879022177004811151/50000000000000000000)
  directionLo := (98234948866940539171/25000000000000000000)
  directionHi := (78587959093552431337/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree063.table
  base := (34723109929258790142305371026100357006363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-2163894563336709038360305930577700000000000000)
      constant := (38756553022742323525051693401965615699007227649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree063.table
  base := (34723063491421156873604986628743775034693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-16532383447633070145359891194237418200000000000000)
      constant := (296386812215791435756902308752013117677112521982874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98234948866940539171/25000000000000000000)
  centralHi := (78587959093552431337/20000000000000000000)
  directionLo := (396095989105963281081/100000000000000000000)
  directionHi := (198047994552981640541/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree064.table
  base := (18628861891268396589556190225588859697171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-6588827746485835116054818769585900000000000000)
      constant := (119854365091657569713050142279012681951201902198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree064.table
  base := (37257682843207538249539796901899854828647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-16779795031444769853338798415362739800000000000000)
      constant := (305524844598716613735352377246116672597242315749246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396095989105963281081/100000000000000000000)
  centralHi := (198047994552981640541/50000000000000000000)
  directionLo := (399227231422677387683/100000000000000000000)
  directionHi := (99806807855669346921/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree065.table
  base := (3985553111023573303200291285027455433319/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-6685971802961543117028719747438700000000000000)
      constant := (123493474658053374230584383201229606255542497110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree065.table
  base := (39855494993437318822694747165006102586831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-17027206615256469561317705636488061400000000000000)
      constant := (314801562858212741841565567850979428884384644695758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399227231422677387683/100000000000000000000)
  centralHi := (99806807855669346921/25000000000000000000)
  directionLo := (6286470390369646451/1562500000000000000)
  directionHi := (80466820996731474573/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree066.table
  base := (42516520749696186981931084014677642688731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-2261038619812417039334206908430500000000000000)
      constant := (42395662420325229592805803417294169990381678913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree066.table
  base := (10629122216307044045031194582818520085431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-17274618199068169269296612857613383000000000000000)
      constant := (324216965715688386474320724497273237727882237402232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6286470390369646451/1562500000000000000)
  centralHi := (80466820996731474573/20000000000000000000)
  directionLo := (81083434006357983701/20000000000000000000)
  directionHi := (202708585015894959253/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree067.table
  base := (45240683119948860813637772561830638725143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-6880259915912959118976521703144300000000000000)
      constant := (130934902465745517447297132352966194248321012767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree067.table
  base := (4524065495225804850159824425469484417023/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-17522029782879868977275520078738704600000000000000)
      constant := (333771052073840028510385579784170031313263839688140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81083434006357983701/20000000000000000000)
  centralHi := (202708585015894959253/50000000000000000000)
  directionLo := (408476965666572051697/100000000000000000000)
  directionHi := (204238482833286025849/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree068.table
  base := (24014004995325135990737148066497814865373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-6977403972388667119950422680997100000000000000)
      constant := (134737219898960406777610014434547078725254215274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree068.table
  base := (2401399254458041965077747040719993873049/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-17769441366691568685254427299864026200000000000000)
      constant := (343463820990149110895157965282159227634665762521640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408476965666572051697/100000000000000000000)
  centralHi := (204238482833286025849/50000000000000000000)
  directionLo := (82302802188930240049/20000000000000000000)
  directionHi := (205757005472325600123/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree069.table
  base := (2543924714280031739396398445413381575487/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-2358182676288125040308107886283300000000000000)
      constant := (46197979746526749564015201151220631391321798020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree069.table
  base := (50878472256313089073439465621282783456039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-18016852950503268393233334520989347800000000000000)
      constant := (353295271654348794892725327641951899238080536731902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82302802188930240049/20000000000000000000)
  centralHi := (205757005472325600123/50000000000000000000)
  directionLo := (207264402953895542381/50000000000000000000)
  directionHi := (414528805907791084763/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree070.table
  base := (53792129915572674827821479147608269125221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-7171692085340083121898224636702700000000000000)
      constant := (142505060211342890978115409953976839561942151549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree070.table
  base := (13448027603441250636378289987188855239169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-18264264534314968101212241742114669400000000000000)
      constant := (363265403369254814855528884681832591812121539888968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207264402953895542381/50000000000000000000)
  centralHi := (414528805907791084763/100000000000000000000)
  directionLo := (208760916272014239099/50000000000000000000)
  directionHi := (417521832544028478199/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree071.table
  base := (28384455817997182037564872010936174422139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6390000000000000000000000000000000000000000
      center := (34239)
      previous := (0)
      next := (30300)
      square := (1289522873571345145671251918400000000000000)
      linear := (-102377973828391424265804586120500000000000000)
      constant := (2062965951778976694314178900741076430911493642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree071.table
  base := (56768894359880409450320978647589027351877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 16257580000000000000000000000000000000000000000
      center := (87201683)
      previous := (0)
      next := (76999875)
      square := (3280832751004073460620036269724800000000000000)
      linear := (-260727832649671377594241534693521000000000000000)
      constant := (5258791768090823323711965586930833741929532847766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208760916272014239099/50000000000000000000)
  centralHi := (417521832544028478199/100000000000000000000)
  directionLo := (420493555687252338141/100000000000000000000)
  directionHi := (210246777843626169071/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree072.table
  base := (59808834925715857077794160693575743466309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-2455326732763833041282008864136100000000000000)
      constant := (50163502043117854769435010899148945968440991007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree072.table
  base := (11961763922186962179355482865257664690451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-18759087701938367517170056184365312600000000000000)
      constant := (383621707632378699132147032757591147503295474084590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420493555687252338141/100000000000000000000)
  centralHi := (210246777843626169071/50000000000000000000)
  directionLo := (52930552982494933069/12500000000000000000)
  directionHi := (423444423859959464553/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree073.table
  base := (62911895883671153587402037788885399174251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-7463124254767207124819927570261100000000000000)
      constant := (154564830693494084648840166793528641675136593619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree073.table
  base := (31455941149249258115806952981842533421801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-19006499285750067225148963405490634200000000000000)
      constant := (394007879216517277593108875103104124090007969722436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52930552982494933069/12500000000000000000)
  centralHi := (423444423859959464553/100000000000000000000)
  directionLo := (426374870063513045917/100000000000000000000)
  directionHi := (213187435031756522959/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree074.table
  base := (66078091140735001792787587248238245375819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-7560268311242915125793828548113900000000000000)
      constant := (158693556115875062768491323602387520954455532211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree074.table
  base := (33039039540959880227663924669267862053093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-19253910869561766933127870626615955800000000000000)
      constant := (404532729901256706782928727515448173884351156468148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426374870063513045917/100000000000000000000)
  centralHi := (213187435031756522959/50000000000000000000)
  directionLo := (85857062503969295423/20000000000000000000)
  directionHi := (107321328129961619279/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree075.table
  base := (13861483556897886357616100272711798410561/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-2552470789239541042255909841988900000000000000)
      constant := (54292227421454335930199691044538602636814570015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree075.table
  base := (554459256589077766675421782069169788489/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-19501322453373466641106777847741277400000000000000)
      constant := (415196259353288907743918134632671975365824409500250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85857062503969295423/20000000000000000000)
  centralHi := (107321328129961619279/25000000000000000000)
  directionLo := (43217615536820964647/10000000000000000000)
  directionHi := (432176155368209646471/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree076.table
  base := (18149968323740996578689748055260741586253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-7754556424194331127741630503819500000000000000)
      constant := (167114209024629380039801540391352098340106849428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree076.table
  base := (4537491485961213114052228466086109148613/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-19748734037185166349085685068866599000000000000000)
      constant := (425998467284242221341897464932225655843894158870944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43217615536820964647/10000000000000000000)
  centralHi := (432176155368209646471/100000000000000000000)
  directionLo := (27190486832515257137/6250000000000000000)
  directionHi := (435047789320244114193/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree077.table
  base := (7595545548970923517939353136468879613657/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-7851700480670039128715531481672300000000000000)
      constant := (171406136297658631317653021099076065991920044330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree077.table
  base := (75955447023672523667784673272188755374429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-19996145620996866057064592289991920600000000000000)
      constant := (436939353444388557918893289449090505805761486894922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27190486832515257137/6250000000000000000)
  centralHi := (435047789320244114193/100000000000000000000)
  directionLo := (437900592276393403209/100000000000000000000)
  directionHi := (43790059227639340321/10000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree078.table
  base := (4960885154800811373690608728135684336271/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-2649614845715249043229810819841700000000000000)
      constant := (58584154665872199061849595136462935267478821328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree078.table
  base := (79374154943186909396048255533748726766639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-20243557204808565765043499511117242200000000000000)
      constant := (448018917617261120844593458164153134039678101602702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437900592276393403209/100000000000000000000)
  centralHi := (43790059227639340321/10000000000000000000)
  directionLo := (88146985981280326241/20000000000000000000)
  directionHi := (220367464953200815603/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree079.table
  base := (82855992614679828011861064848567442969427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-8045988593621455130663333437377900000000000000)
      constant := (180153192050025735999783849714216356320079933563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree079.table
  base := (82855985906837487495626497494664050180741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-20490968788620265473022406732242563800000000000000)
      constant := (459237159615047402605260947620309307519455619994138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88146985981280326241/20000000000000000000)
  centralHi := (220367464953200815603/50000000000000000000)
  directionLo := (443551156196424973411/100000000000000000000)
  directionHi := (110887789049106243353/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree080.table
  base := (86400944477573459743819489923506272535893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-8143132650097163131637234415230700000000000000)
      constant := (184608320390201816951633804288635556078680929517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree080.table
  base := (86400938501591225431819593696314604833847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-20738380372431965181001313953367885400000000000000)
      constant := (470594079274642670460459815288640557792108045602846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443551156196424973411/100000000000000000000)
  centralHi := (110887789049106243353/25000000000000000000)
  directionLo := (55793701745634169687/12500000000000000000)
  directionHi := (446349613965073357497/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree081.table
  base := (90009016826072240906527083395602601881201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-2746758902190957044203711797694500000000000000)
      constant := (63039282987304506608412567793119398148249402723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree081.table
  base := (45004505749577574892329145075448781546361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-20985791956243664888980221174493207000000000000000)
      constant := (482089676454266518330617592584993018046873324862596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55793701745634169687/12500000000000000000)
  centralHi := (446349613965073357497/100000000000000000000)
  directionLo := (56141329418814007643/12500000000000000000)
  directionHi := (89826127070102412229/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree082.table
  base := (93680208581716691605512493698858712478767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-8337420763048579133585036370936300000000000000)
      constant := (193681777716232216477263276237186520926449180023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree082.table
  base := (23420050957706417568379828569230305526669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-21233203540055364596959128395618528600000000000000)
      constant := (493723951030559753997285646851993292346889080588968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56141329418814007643/12500000000000000000)
  centralHi := (89826127070102412229/20000000000000000000)
  directionLo := (451894542270582483997/100000000000000000000)
  directionHi := (225947271135291241999/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree083.table
  base := (97414518805235828729160455144291030769611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-8434564819524287134558937348789100000000000000)
      constant := (198300106610544121674919649873077039774986481459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree083.table
  base := (97414514565890258232634414744351368585017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-21480615123867064304938035616743850200000000000000)
      constant := (505496902896091330378783231776688603552450844819906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451894542270582483997/100000000000000000000)
  centralHi := (225947271135291241999/50000000000000000000)
  directionLo := (227320823428873253623/50000000000000000000)
  directionHi := (454641646857746507247/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree084.table
  base := (101211946677831164478292194307874184989347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-2843902958666665045177612775547300000000000000)
      constant := (67657611869233722275081960838518381299593894681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree084.table
  base := (25302985723265950856995733412953103669791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-21728026707678764012916942837869171800000000000000)
      constant := (517408531957215566139797639429940806984141749748152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227320823428873253623/50000000000000000000)
  centralHi := (454641646857746507247/100000000000000000000)
  directionLo := (457372251870517949179/100000000000000000000)
  directionHi := (22868612593525897459/5000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree085.table
  base := (105072491485074977752266452056507356076063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-8628852932475703136506739304494700000000000000)
      constant := (207699964675290480649626980879011182237814902247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree085.table
  base := (4202899524180772836786951296920933645489/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-21975438291490463720895850058994493400000000000000)
      constant := (529458838132228829060213440408656481753880657550050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457372251870517949179/100000000000000000000)
  centralHi := (22868612593525897459/5000000000000000000)
  directionLo := (460086651082916265451/100000000000000000000)
  directionHi := (115021662770729066363/25000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree086.table
  base := (54498076301522725337418425360808670613177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-8725996988951411137480640282347500000000000000)
      constant := (212481493785005354192835523054999657154098454626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree086.table
  base := (13624518697767281141227749113826907238781/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-22222849875302163428874757280119815000000000000000)
      constant := (541647821349782424193235157899617187073345076726864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460086651082916265451/100000000000000000000)
  centralHi := (115021662770729066363/25000000000000000000)
  directionLo := (92557025930672115539/20000000000000000000)
  directionHi := (14462035301667518053/3125000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree087.table
  base := (22596585897275445275505189536805176985337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-2941047015142373046151513753400100000000000000)
      constant := (72439140970701035526368518649777023457746257255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree087.table
  base := (112982926785661190047326908197677401359913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-22470261459113863136853664501245136600000000000000)
      constant := (553975481547514847813049892195880389284286350172834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92557025930672115539/20000000000000000000)
  centralHi := (14462035301667518053/3125000000000000000)
  directionLo := (18618718578972609199/4000000000000000000)
  directionHi := (58183495559289403747/12500000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree088.table
  base := (58516410828976718173372932401284915455209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-8920285101902827139428442238053100000000000000)
      constant := (222207752034937422600844111118618990658574754242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree088.table
  base := (23406563848493425531041570219340869487133/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-22717673042925562844832571722370458200000000000000)
      constant := (566441818670872014678858495800852772919960141993970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18618718578972609199/4000000000000000000)
  centralHi := (58183495559289403747/12500000000000000000)
  directionLo := (234067712251950188813/50000000000000000000)
  directionHi := (468135424503900377627/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree089.table
  base := (7571614293750348019019621401736196498811/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-9017429158378535140402343215905900000000000000)
      constant := (227152481134554562624502319477226611983272900144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree089.table
  base := (121145826538749217196072157765814116156897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-22965084626737262552811478943495779800000000000000)
      constant := (579046832672088689820005636765394562135705323257746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234067712251950188813/50000000000000000000)
  centralHi := (468135424503900377627/100000000000000000000)
  directionLo := (470787771080591721901/100000000000000000000)
  directionHi := (235393885540295860951/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree090.table
  base := (25064390049284359702305863574591938727743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-3038191071618081047125414731252900000000000000)
      constant := (77383870064781466439626353861973769446898286945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree090.table
  base := (125321948311889260221134944710809021572403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-23212496210548962260790386164621101400000000000000)
      constant := (591790523509308283204258642451502808183838979709654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470787771080591721901/100000000000000000000)
  centralHi := (235393885540295860951/50000000000000000000)
  directionLo := (757480413155282601/160000000000000000)
  directionHi := (236712629111025812813/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree091.table
  base := (25912237195218704938240515091240841768037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-9211717271329951142350145171611500000000000000)
      constant := (237205139199738556507260530844630628750870353265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree091.table
  base := (129561184243861892946143889847384185870497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-23459907794360661968769293385746423000000000000000)
      constant := (604672891145821502995981260307230902666923769782546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (757480413155282601/160000000000000000)
  centralHi := (236712629111025812813/50000000000000000000)
  directionLo := (238024066454529386033/50000000000000000000)
  directionHi := (476048132909058772067/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree092.table
  base := (2677270712143091852339135214536787104871/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-9308861327805659143324046149464300000000000000)
      constant := (242313068137949048638550231206881974708044619950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree092.table
  base := (133863534055524099350208133804207439713751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-23707319378172361676748200606871744600000000000000)
      constant := (617693935549407200802926995128341750192964536276318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238024066454529386033/50000000000000000000)
  centralHi := (476048132909058772067/100000000000000000000)
  directionLo := (478656635355434627429/100000000000000000000)
  directionHi := (47865663535543462743/10000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree093.table
  base := (138228998891988774528561348645702051065827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-3135335128093789048099315709105700000000000000)
      constant := (82491798999247258358498087994057852118268501721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree093.table
  base := (34557249375416643962448172455788687332501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-23954730961984061384727107827997066200000000000000)
      constant := (630853656691761156549845239131699441646248653655272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478656635355434627429/100000000000000000000)
  centralHi := (47865663535543462743/10000000000000000000)
  directionLo := (481250999264801668107/100000000000000000000)
  directionHi := (120312749816200417027/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree094.table
  base := (142657575612898992096768780847816308158703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-9503149440757075145271848105169900000000000000)
      constant := (252692125769240037071372996695044778084852196407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree094.table
  base := (3566439359168031984167764580274323338219/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-24202142545795761092706015049122387800000000000000)
      constant := (644152054548000605825647788245465849747217335805680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481250999264801668107/100000000000000000000)
  centralHi := (120312749816200417027/25000000000000000000)
  directionLo := (483831452074950126233/100000000000000000000)
  directionHi := (241915726037475063117/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree095.table
  base := (147149265578347055360685047492405046724897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-9600293497232783146245749083022700000000000000)
      constant := (257963254443753938485850629013029424564861851993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree095.table
  base := (147149264461034657174921658224903229767003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-24449554129607460800684922270247709400000000000000)
      constant := (657589129096234063209667149471718418476387571692454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483831452074950126233/100000000000000000000)
  centralHi := (241915726037475063117/50000000000000000000)
  directionLo := (486398215190536432057/100000000000000000000)
  directionHi := (243199107595268216029/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree096.table
  base := (151704068619685713527086182487904515406869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (810323)
      previous := (0)
      next := (717100)
      square := (30518708007855168447552962068800000000000000)
      linear := (-3232479184569497049073216686958500000000000000)
      constant := (87762927671210707399229794272839779986498079887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree096.table
  base := (151704067617628984350685598219164509332639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-24696965713419160508663829491373031000000000000000)
      constant := (671164880317187487281626837921088907459816488590702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486398215190536432057/100000000000000000000)
  centralHi := (243199107595268216029/50000000000000000000)
  directionLo := (24447575210239358779/5000000000000000000)
  directionHi := (488951504204787175581/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree097.table
  base := (156321984588315923699268376308241516765647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-9794581610184199148193551038728300000000000000)
      constant := (268668711472132798229708702977126109374140638743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree097.table
  base := (156321983689385260879643895914241830985321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-24944377297230860216642736712498352600000000000000)
      constant := (684879308193879105764527468070058511416791378380578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell166.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24447575210239358779/5000000000000000000)
  centralHi := (488951504204787175581/100000000000000000000)
  directionLo := (491491529110836900247/100000000000000000000)
  directionHi := (61436441138854612531/12500000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree098.table
  base := (80501506676605863665830922392902417304817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (2430969)
      previous := (0)
      next := (2151300)
      square := (91556124023565505342658886206400000000000000)
      linear := (-9891725666659907149167452016581100000000000000)
      constant := (274103039813311449868654633950949379541404484946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree098.table
  base := (80501506273295265785358467514496631367477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1154288180000000000000000000000000000000000000000
      center := (6191319493)
      previous := (0)
      next := (5466991125)
      square := (232939125321289215704022575150460800000000000000)
      linear := (-25191788881042559924621643933623674200000000000000)
      constant := (698732412711336305561375755667401461447459187504372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell166.Kernel098
