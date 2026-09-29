import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell096.Parameters
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch000_049
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch050_099
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch100_149
import ForestUnimodality.BinomialMassData.Q7339_14214.Batch150_199
import ForestUnimodality.BinomialMassData.Q107_207.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_207.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_207.Batch100_149
import ForestUnimodality.BinomialMassData.Q107_207.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree000.table
  base := (899415097637477646730275177/10000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (61193278067236289707864216000000000000)
      linear := (-2693041815028840609003157900000000000)
      constant := (89941509763747764673027517700000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree000.table
  base := (899415097637477646730275177/10000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (61193278067236289707864216000000000000)
      linear := (-2693041815028840609003157900000000000)
      constant := (89941509763747764673027517700000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree001.table
  base := (61346446741157589346270316654375006934071/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-16638798807034447061797229849239825500000000000)
      constant := (12398771960934971622732290764011924595194422147516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree001.table
  base := (245154327175142404021522961041219599988993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-14130669902773019763670726766125500000000000)
      constant := (10508419015246441180275808099421774139928361057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49971403056949760723/100000000000000000000)
  directionHi := (12492850764237440181/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree002.table
  base := (283728063066195447300924878179900624470147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-65194954646027121664493179949069331000000000000)
      constant := (14365312038569773932074715393102035843743041919003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree002.table
  base := (56652053287930643409057448433662801134469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (5244141543806015555384547582768000000000000)
      linear := (-11073747624754074228426228787186200000000000)
      constant := (2433327238791918740844220550983197765810862181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49971403056949760723/100000000000000000000)
  centralHi := (12492850764237440181/25000000000000000000)
  directionLo := (70670235933950693029/100000000000000000000)
  directionHi := (7067023593395069303/10000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree003.table
  base := (88150162625008877461210242837491971989181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-5395128426554741622521772233314389500000000000)
      constant := (498949866397527746328075182980322375260774030141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree003.table
  base := (2199223675657737226909586447697279514373/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4761000000000000000000000000000000000000000
      center := (85698)
      previous := (42849)
      next := (42849)
      square := (291341196878111975299141532376000000000000)
      linear := (-916401516022163363965787048217900000000000)
      constant := (84484515926764041709613936343653682143438824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70670235933950693029/100000000000000000000)
  centralHi := (7067023593395069303/10000000000000000000)
  directionLo := (2704781531879365517/3125000000000000000)
  directionHi := (17310601804027939309/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree004.table
  base := (29617695525543035071102128524846273893709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-64514834354971788373145310225124345500000000000)
      constant := (3059270133705984081937435151044497995148652312682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree004.table
  base := (118212591241084041690982645964352213889773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-109583534760219034371710524743291000000000000)
      constant := (5179773543910339178981321820137052012962883277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2704781531879365517/3125000000000000000)
  centralHi := (17310601804027939309/20000000000000000000)
  directionLo := (49971403056949760723/50000000000000000000)
  directionHi := (99942806113899521447/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree005.table
  base := (42826690995511177797371308189316635126353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-80473512870950902143594670350419185500000000000)
      constant := (2267906067169841138787243950168666510516135409497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree005.table
  base := (21368090339359356668797642086469539323811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-68345466539221682993250107573485500000000000)
      constant := (1920269040555418527677007781257444080971955078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49971403056949760723/50000000000000000000)
  centralHi := (99942806113899521447/100000000000000000000)
  directionLo := (55869727083190229807/50000000000000000000)
  directionHi := (22347890833276091923/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree006.table
  base := (13141753893838866202927190763125401485747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (686853057262197765766353892661552000000000000)
      linear := (-4285875172752445151735290243365067800000000000)
      constant := (80439134246147311345768089718852026127651369267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree006.table
  base := (3278948522564045617043097372076114364711/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4761000000000000000000000000000000000000000
      center := (85698)
      previous := (42849)
      next := (42849)
      square := (291341196878111975299141532376000000000000)
      linear := (-1819981459962974417792110061673900000000000)
      constant := (34064320649662711349378263442396160980778142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55869727083190229807/50000000000000000000)
  centralHi := (22347890833276091923/20000000000000000000)
  directionLo := (122404439220482389111/100000000000000000000)
  directionHi := (15300554902560298639/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree007.table
  base := (52605494817668066281617684472191278702653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-224781739805818259368986781202017731000000000000)
      constant := (3065741785643903329592841108258707704376437868197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree007.table
  base := (2100326951593230348832219682055745338641/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (5244141543806015555384547582768000000000000)
      linear := (-38181145942978405843215919190866200000000000)
      constant := (519478602686341920679445325083044560077141045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122404439220482389111/100000000000000000000)
  centralHi := (15300554902560298639/12500000000000000000)
  directionLo := (66105952576830959763/50000000000000000000)
  directionHi := (132211905153661919527/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree008.table
  base := (21655926396225408528633894633279238457901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-128349548418888243454942750726303705500000000000)
      constant := (1360312303318510579071427209339432411648189206549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree008.table
  base := (4323497527921454406463884647243254659951/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42849000000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (2622070771903007777692273791384000000000000)
      linear := (-21801312803311636083086928635801100000000000)
      constant := (230573248837069440163143074979319018924240399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66105952576830959763/50000000000000000000)
  centralHi := (132211905153661919527/100000000000000000000)
  directionLo := (141340471867901386059/100000000000000000000)
  directionHi := (7067023593395069303/5000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree009.table
  base := (1813767994233656318089752607550286031317/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5612161000000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (343426528631098882883176946330776000000000000)
      linear := (-3206849487441496827230935796702189900000000000)
      constant := (27844382416015551235901616788870800957604092074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree009.table
  base := (18105840022962571280176718502721303714127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (47610)
      previous := (23805)
      next := (23805)
      square := (161856220487839986277300851320000000000000)
      linear := (-1513089668835436373121351708405500000000000)
      constant := (13114136454640071495233954990819069664773183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141340471867901386059/100000000000000000000)
  centralHi := (7067023593395069303/5000000000000000000)
  directionLo := (14991420917084928217/10000000000000000000)
  directionHi := (149914209170849282171/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree010.table
  base := (15338781267398746763807514684369588216847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-160266905450846470995841470976893385500000000000)
      constant := (1190255789866355417650445985045041480689834487303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree010.table
  base := (3827859690413649735366989061251127638921/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-136113962334782512030224333582685500000000000)
      constant := (1009363168952085740008069708850553272800503716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14991420917084928217/10000000000000000000)
  centralHi := (149914209170849282171/100000000000000000000)
  directionLo := (158023451534262087543/100000000000000000000)
  directionHi := (19752931441782760943/12500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree011.table
  base := (26068055137477944435242709422116937720331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-352451167933651169532581662204376451000000000000)
      constant := (2321426354558418223208645701449439946321234907619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree011.table
  base := (13009983806649361824764971980444299118557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-149667661493894677837619178784525500000000000)
      constant := (984609559763009473238568018763368272931048893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158023451534262087543/100000000000000000000)
  centralHi := (19752931441782760943/12500000000000000000)
  directionLo := (82868197093760593653/50000000000000000000)
  directionHi := (165736394187521187307/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree012.table
  base := (5546035625718426294806849117607442632109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-21353806942533855392971132358609229500000000000)
      constant := (128637230701372993736472997860868214699318955098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree012.table
  base := (4428255145308099689629617612530030069397/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9522000000000000000000000000000000000000000
      center := (171396)
      previous := (85698)
      next := (85698)
      square := (582682393756223950598283064752000000000000)
      linear := (-7254282695689193050889512177171800000000000)
      constant := (43661243467511951051747569058949073160399117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82868197093760593653/50000000000000000000)
  centralHi := (165736394187521187307/100000000000000000000)
  directionLo := (2704781531879365517/1562500000000000000)
  directionHi := (173106018040279393089/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree013.table
  base := (4715368982199195022393483004284191646293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-208142940998783812307189551352777905500000000000)
      constant := (1177170905770108535869327730950348516679324645114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree013.table
  base := (18823008026645888433312599614988649891589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-353550119624238018904817738376411000000000000)
      constant := (1998318445344811460925777224848131659204697061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2704781531879365517/1562500000000000000)
  centralHi := (173106018040279393089/100000000000000000000)
  directionLo := (180174456028710303367/100000000000000000000)
  directionHi := (22521807003588787921/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree014.table
  base := (15989348252959660462816386054520076320263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-448203239029525852155277822956145491000000000000)
      constant := (2432449573537432132460301687702253123374431665087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree014.table
  base := (15954748929950423633985130837244017155769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-380657517942462350519607428780091000000000000)
      constant := (2065175390101901063479523725059502891107545881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180174456028710303367/100000000000000000000)
  centralHi := (22521807003588787921/12500000000000000000)
  directionLo := (186975869375493987763/100000000000000000000)
  directionHi := (46743967343873496941/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree015.table
  base := (13487978136576412741496138648280698574143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-53346732895720453299575171467415019000000000000)
      constant := (282862636350422137387067545079826376090560953023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree015.table
  base := (13456865918470781401485039816338648644191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (856980)
      previous := (428490)
      next := (428490)
      square := (2913411968781119752991415323760000000000000)
      linear := (-45307212917854075792710791020419000000000000)
      constant := (240212735171804356979618142550373306194993351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186975869375493987763/100000000000000000000)
  centralHi := (46743967343873496941/25000000000000000000)
  directionLo := (19353841182618482561/10000000000000000000)
  directionHi := (193538411826184825611/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree016.table
  base := (11296677132579192066768641811566522790227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-512037953093442307237075263457324851000000000000)
      constant := (2691218932367255874370853220479290468980308354923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree016.table
  base := (450749807601519734668985185993101098433/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (5244141543806015555384547582768000000000000)
      linear := (-86974462915782202749837361917490200000000000)
      constant := (457187776773737556657971434791367144833778085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19353841182618482561/10000000000000000000)
  centralHi := (193538411826184825611/100000000000000000000)
  directionLo := (199885612227799042893/100000000000000000000)
  directionHi := (99942806113899521447/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree017.table
  base := (2341862388347716261416711747492363302771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-271977655062700267388986991853957265500000000000)
      constant := (1433195476721952446721885767172706469011566766358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree017.table
  base := (4671214545491624752255955056535348203331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-230989856448567672681988249995565500000000000)
      constant := (1217596627283595967064976904467166635164530019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199885612227799042893/100000000000000000000)
  centralHi := (99942806113899521447/50000000000000000000)
  directionLo := (51509343266029279517/25000000000000000000)
  directionHi := (206037373064117118069/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree018.table
  base := (1915335870160050689807612813790170174177/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-31992925953186597906604039108805789500000000000)
      constant := (170517352802740141308489571862990563969758732994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree018.table
  base := (1527797386768480958028068393346926511297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (19044)
      previous := (9522)
      next := (9522)
      square := (64742488195135994510920340528000000000000)
      linear := (-1207622496828048585132756025666200000000000)
      constant := (6439529845961976580674574538320124124476113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51509343266029279517/25000000000000000000)
  centralHi := (206037373064117118069/100000000000000000000)
  directionLo := (212010707801852079089/100000000000000000000)
  directionHi := (21201070780185207909/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree019.table
  base := (6146227241455148481573169958447591518609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-607790024189316989859771424209093891000000000000)
      constant := (3298360170291292991976715223781919619482013836441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree019.table
  base := (3063150727479125946547953432304017942057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-258097254766792004296777940399245500000000000)
      constant := (1401505845190232924757204319547989364799200393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212010707801852079089/100000000000000000000)
  centralHi := (21201070780185207909/10000000000000000000)
  directionLo := (108910147996091748411/50000000000000000000)
  directionHi := (217820295992183496823/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree020.table
  base := (479533082397228105959183791078392232273/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (3090838757679889945948592516976984000000000000)
      linear := (-63970738122127521740067014445968357100000000000)
      constant := (355218227442087137301729481123497374457989247577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree020.table
  base := (4777614943669578535322060252292184753763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-543301907851808340208345571202171000000000000)
      constant := (3019053021720665652251126784551887824513990787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108910147996091748411/50000000000000000000)
  centralHi := (217820295992183496823/100000000000000000000)
  directionLo := (55869727083190229807/25000000000000000000)
  directionHi := (223478908332760919229/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree021.table
  base := (3586218789656342160920099627202168766239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-74624970917025938326840984967808139000000000000)
      constant := (425516162355507602359340841578795122165304632479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree021.table
  base := (892626035655098957002702113165605114843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (428490)
      previous := (214245)
      next := (214245)
      square := (1456705984390559876495707661880000000000000)
      linear := (-31689405898335148434618625644769500000000000)
      constant := (180842931526708508638156855739792391903535046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55869727083190229807/25000000000000000000)
  centralHi := (223478908332760919229/100000000000000000000)
  directionLo := (228997737091619937497/100000000000000000000)
  directionHi := (114498868545809968749/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree022.table
  base := (19531427862416263650962089742645264637/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-351771047642595836241233792480431465500000000000)
      constant := (2064898349774087233120682223582375252133539520832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree022.table
  base := (1243056691339541640403547850749054056673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-298758352244128501718962476004765500000000000)
      constant := (1755281490547053776415137355474007217274381377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228997737091619937497/100000000000000000000)
  centralHi := (114498868545809968749/50000000000000000000)
  directionLo := (29298332054850732791/12500000000000000000)
  directionHi := (234386656438805862329/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree023.table
  base := (47526310869032913223311217092226536769/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 477405000000000000000000000000000000000000000
      center := (8593290)
      previous := (4296645)
      next := (4296645)
      square := (29213976915688940887982916039480000000000000)
      linear := (-695141259278969659757435071088329500000000000)
      constant := (4207781520320119886559852974812803361315854224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree023.table
  base := (1508555106283411620199193613536835407047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (14580)
      previous := (7290)
      next := (7290)
      square := (49566555234461394663370014960000000000000)
      linear := (-1180763899445144300666757358059000000000000)
      constant := (7154145362205566884954209183113483667970807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29298332054850732791/12500000000000000000)
  centralHi := (234386656438805862329/100000000000000000000)
  directionLo := (239654430044685260961/100000000000000000000)
  directionHi := (119827215022342630481/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree024.table
  base := (317630232799078611793161237449969901057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-42632044963839340420236945859002349500000000000)
      constant := (266393126663029560693163215350498718529885954177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree024.table
  base := (312213508984238347829394653798848382097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (428490)
      previous := (214245)
      next := (214245)
      square := (1456705984390559876495707661880000000000000)
      linear := (-36207305618039203703750240712049500000000000)
      constant := (226474346614460525859574531412644317147163817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239654430044685260961/100000000000000000000)
  centralHi := (119827215022342630481/50000000000000000000)
  directionLo := (244808878440964778223/100000000000000000000)
  directionHi := (15300554902560298639/6250000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree025.table
  base := (-84024371488094630163241475432295677679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-399647083190533177552581872856315985500000000000)
      constant := (2579477435079144459855765779046780627265352111129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree025.table
  base := (-88792167090276889701335978688498132703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-339419449721464999141147011610285500000000000)
      constant := (2193032119176821327088468225765064043511809153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244808878440964778223/100000000000000000000)
  centralHi := (15300554902560298639/6250000000000000000)
  directionLo := (7808031727648400113/3125000000000000000)
  directionHi := (249857015284748803617/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree026.table
  base := (-112331621280186680695700897681960985133/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-415605761706512291323031232981610825500000000000)
      constant := (2771492690253036502305634122965765949105739913132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree026.table
  base := (-907032862216906358314130982239353998703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-705946297761154329897083713624251000000000000)
      constant := (4712711518909235743670969531798911920509575153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7808031727648400113/3125000000000000000)
  centralHi := (249857015284748803617/100000000000000000000)
  directionLo := (1990665307101538827/781250000000000000)
  directionHi := (254805159308996969857/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree027.table
  base := (-62585400088101991332304756028814278223/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (686853057262197765766353892661552000000000000)
      linear := (-19180641787666284670821359693640251800000000000)
      constant := (132150212309119939290865823419802696257568650485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree027.table
  base := (-196498552730165278240811716311298960893/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (47610)
      previous := (23805)
      next := (23805)
      square := (161856220487839986277300851320000000000000)
      linear := (-4525022815304806552542428419925500000000000)
      constant := (31210705527655232561263977386443791398750412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1990665307101538827/781250000000000000)
  centralHi := (254805159308996969857/100000000000000000000)
  directionLo := (8114344595638096551/3125000000000000000)
  directionHi := (259659027060419089633/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree028.table
  base := (-2172824374227466606182766425394404366619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-895046237476941037727859906464401011000000000000)
      constant := (6369932434302892546091150418760826525758880317069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree028.table
  base := (-2179268231323165013841132766915242221357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-760161094397602993126663094431611000000000000)
      constant := (5416040457080754485687833652916596786057073907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8114344595638096551/3125000000000000000)
  centralHi := (259659027060419089633/100000000000000000000)
  directionLo := (264423810307323839053/100000000000000000000)
  directionHi := (132211905153661919527/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree029.table
  base := (-2728992135924447273087328207696734908881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-926963594508899265268758626714990691000000000000)
      constant := (6812212529147696821080033067768497772153355483431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree029.table
  base := (-341828968404699176005420656549501993289/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-393634246357913662370726392417645500000000000)
      constant := (2896091608378133600712196312855191056358238556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264423810307323839053/100000000000000000000)
  centralHi := (132211905153661919527/50000000000000000000)
  directionLo := (269104241105419423373/100000000000000000000)
  directionHi := (134552120552709711687/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree030.table
  base := (-1619007560042704653403599421444575186329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-53271163974492082933869852609198909500000000000)
      constant := (404075195128201400407013862218632413977716653031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree030.table
  base := (-648588999971551065321606107780686457039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9522000000000000000000000000000000000000000
      center := (171396)
      previous := (85698)
      next := (85698)
      square := (582682393756223950598283064752000000000000)
      linear := (-18097242022978925696805388338643800000000000)
      constant := (137430090443900260155396721413170151778037321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269104241105419423373/100000000000000000000)
  centralHi := (134552120552709711687/50000000000000000000)
  directionLo := (136852323422369995151/50000000000000000000)
  directionHi := (273704646844739990303/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree031.table
  base := (-3704014606860574255040918016448255152179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-990798308572815720350556067216170051000000000000)
      constant := (7753147220193115377227619317643426973752027560629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree031.table
  base := (-3708319288206698412030999187715466375967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-841483289352275987971032165642651000000000000)
      constant := (6592376851686649433959907608883220981256190017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136852323422369995151/50000000000000000000)
  centralHi := (273704646844739990303/100000000000000000000)
  directionLo := (69557249275275023549/25000000000000000000)
  directionHi := (278228997101100094197/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree032.table
  base := (-516309178887459605864190173202608985543/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-511357832802386973945727393733379865500000000000)
      constant := (4125708868367474615909936328869869235111096416772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree032.table
  base := (-4134228290961940511146672038859645820321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-868590687670500319585821856046331000000000000)
      constant := (7016102718232027420106550819987735036245065471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69557249275275023549/25000000000000000000)
  centralHi := (278228997101100094197/100000000000000000000)
  directionLo := (282680943735802772119/100000000000000000000)
  directionHi := (7067023593395069303/2500000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree033.table
  base := (-1130083727985188317813104636665841792341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-58590723479818454190686305984297189500000000000)
      constant := (487112022028068522681293173634449800071707482198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree033.table
  base := (-4523606979412826204344233123911916180497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (856980)
      previous := (428490)
      next := (428490)
      square := (2913411968781119752991415323760000000000000)
      linear := (-99522009554302739022290171827779000000000000)
      constant := (828378434336318726611965105593022367064653783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282680943735802772119/100000000000000000000)
  centralHi := (7067023593395069303/2500000000000000000)
  directionLo := (287063855396049853167/100000000000000000000)
  directionHi := (17941490962253115823/6250000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree034.table
  base := (-2438043219933503243684448052987588115379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-543275189834345201486626113983969545500000000000)
      constant := (4651408781390606740663925107357092709953258283829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree034.table
  base := (-4878935173553441760053630474522042570907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-922805484306948982815401236853691000000000000)
      constant := (7910180166264246189647358156723458997879205957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287063855396049853167/100000000000000000000)
  centralHi := (17941490962253115823/6250000000000000000)
  directionLo := (291380847342999447687/100000000000000000000)
  directionHi := (36422605917874930961/12500000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree035.table
  base := (-5199830107289961729367712796835200279891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-1118467736700648630514150948218528771000000000000)
      constant := (9855715060033436230189364553726150262558059809941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree035.table
  base := (-5202308132051231621277230321048703834923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-949912882625173314430190927257371000000000000)
      constant := (8380335710205519043587359048541869089377384373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291380847342999447687/100000000000000000000)
  centralHi := (36422605917874930961/12500000000000000000)
  directionLo := (73908701839585707619/25000000000000000000)
  directionHi := (295634807358342830477/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree036.table
  base := (-5493342394239403361824781613476953392039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-127820565970289650895005518718790939000000000000)
      constant := (1158513239914937527000475073160590661774381013721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree036.table
  base := (-5495496191324865648406307040672314068433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (95220)
      previous := (47610)
      next := (47610)
      square := (323712440975679972554601702640000000000000)
      linear := (-12061978777078983284505933551371000000000000)
      constant := (109454280045746710079997319876600345857798943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73908701839585707619/25000000000000000000)
  centralHi := (295634807358342830477/100000000000000000000)
  directionLo := (14991420917084928217/5000000000000000000)
  directionHi := (299828418341698564341/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree037.table
  base := (-1439531151691560592726623942813898791521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-591151225382282542797974194359854065500000000000)
      constant := (5507727015121403069956636192623377524747016836142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree037.table
  base := (-5759995154130154395565806988542652666669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-1004127679261621977659770308064731000000000000)
      constant := (9366498993111855881890929914739922875885900019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14991420917084928217/5000000000000000000)
  centralHi := (299828418341698564341/100000000000000000000)
  directionLo := (303964178101243916899/100000000000000000000)
  directionHi := (3039641781012439169/1000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree038.table
  base := (-5995445501544592980988766328680171118871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-1214219807796523313136847108970297811000000000000)
      constant := (11622155588858016838880065097692168892560112287921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree038.table
  base := (-1499267215807979937973087872224232488629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-515617538789923154637279999234205500000000000)
      constant := (4941194242013003143346592487812756724189471958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303964178101243916899/100000000000000000000)
  centralHi := (3039641781012439169/1000000000000000000)
  directionLo := (308044416752267821161/100000000000000000000)
  directionHi := (154022208376133910581/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree039.table
  base := (-1241275461509479966630182541148912168913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (686853057262197765766353892661552000000000000)
      linear := (-27691936996188478681727685093797499800000000000)
      constant := (272148215053009879337249657924059267633201049007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree039.table
  base := (-6207785172566940804152226379124062187717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (856980)
      previous := (428490)
      next := (428490)
      square := (2913411968781119752991415323760000000000000)
      linear := (-117593608433118960098816632096899000000000000)
      constant := (1157046599997177520421966612312791339924279363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308044416752267821161/100000000000000000000)
  centralHi := (154022208376133910581/50000000000000000000)
  directionLo := (12482852482712434121/4000000000000000000)
  directionHi := (156035656033905426513/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree040.table
  base := (-1278365233566281161150698908519485278249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (6181677515359779891897185033953968000000000000)
      linear := (-255610904372087953643728909894295434200000000000)
      constant := (2577790105407715615056223004232540460832031325199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree040.table
  base := (-639304634002215159523485183629436268127/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42849000000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (2622070771903007777692273791384000000000000)
      linear := (-108544987421629497250413937927577100000000000)
      constant := (1095955308010943283640070475514146285347026177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12482852482712434121/4000000000000000000)
  centralHi := (156035656033905426513/50000000000000000000)
  directionLo := (316046903068524175087/100000000000000000000)
  directionHi := (19752931441782760943/6250000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree041.table
  base := (-3276278932933344629796815775339207974679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-654985939446198997879771634861033425500000000000)
      constant := (6774479729258145194102010312010209523852557758129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree041.table
  base := (-6553614707007041698553624118910117541673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-1112557272534519304118929069679451000000000000)
      constant := (11520756858863456525771010092323971373456853623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316046903068524175087/100000000000000000000)
  centralHi := (19752931441782760943/6250000000000000000)
  directionLo := (159986551046240480177/50000000000000000000)
  directionHi := (63994620418496192071/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree042.table
  base := (-3344609783440846417336309937937938040321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-74549401995797567961135666109592029500000000000)
      constant := (790370210214415606226132254863398515209694056319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree042.table
  base := (-3345067197884794621492943039118726822299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (428490)
      previous := (214245)
      next := (214245)
      square := (1456705984390559876495707661880000000000000)
      linear := (-63314703936263535318539931115729500000000000)
      constant := (672055729791248063170241681029374741599034461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159986551046240480177/50000000000000000000)
  centralHi := (63994620418496192071/20000000000000000000)
  directionLo := (323851705547717274053/100000000000000000000)
  directionHi := (161925852773858637027/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree043.table
  base := (-1700589547878734270920041165773200069043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-686903296478157225420670355111623105500000000000)
      constant := (7461017939204025622794331218441724811341752225386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree043.table
  base := (-6803149642023703955883193964406451379627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-1166772069170967967348508450486811000000000000)
      constant := (12688268592290353352373438419993960964834362677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323851705547717274053/100000000000000000000)
  centralHi := (161925852773858637027/50000000000000000000)
  directionLo := (327684403519065123221/100000000000000000000)
  directionHi := (163842201759532561611/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree044.table
  base := (-215388623232269001688908445208263246883/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-702861974994136339191119715236917945500000000000)
      constant := (7817526198254748275785874699195581787447819240528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree044.table
  base := (-689312028467318836109700978329850864439/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42849000000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (2622070771903007777692273791384000000000000)
      linear := (-119387946748919229896329814089049100000000000)
      constant := (1329453352336993213735376328122960620309653289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327684403519065123221/100000000000000000000)
  centralHi := (163842201759532561611/50000000000000000000)
  directionLo := (82868197093760593653/25000000000000000000)
  directionHi := (331472788375042374613/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree045.table
  base := (-6959843431760352203523457073089980306387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-159737923002247878435904238969380619000000000000)
      constant := (1818410400968011783963286450214889430533726827693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree045.table
  base := (-108756794585865218642912163993919927377/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (47610)
      previous := (23805)
      next := (23805)
      square := (161856220487839986277300851320000000000000)
      linear := (-7536955961774176731963505131445500000000000)
      constant := (85899884452893658105448878300708423469362144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82868197093760593653/25000000000000000000)
  centralHi := (331472788375042374613/100000000000000000000)
  directionLo := (167609181249570689421/50000000000000000000)
  directionHi := (335218362499141378843/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree046.table
  base := (-56039286087104110877127939308603249479/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190962000000000000000000000000000000000000000
      center := (3437316)
      previous := (1718658)
      next := (1718658)
      square := (11685590766275576355193166415792000000000000)
      linear := (-555598738772094190345571595831763800000000000)
      constant := (6470299751086970222950113954739519128412390025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree046.table
  base := (-1401084325455657861949459793234648990783/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 162000000000000000000000000000000000000000
      center := (2916)
      previous := (1458)
      next := (1458)
      square := (9913311046892278932674002992000000000000)
      linear := (-471869287004023048088044431643800000000000)
      constant := (5501700491443889054130673192850793431746577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167609181249570689421/50000000000000000000)
  centralHi := (335218362499141378843/100000000000000000000)
  directionLo := (169461272625994021673/50000000000000000000)
  directionHi := (338922545251988043347/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree047.table
  base := (-7027916902496187895410985796687862695223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-1501476021084147361004935591225604931000000000000)
      constant := (17879786004542413652644042239492856164776631337873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree047.table
  base := (-7028357977139955252102021343026229574079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-1275201662443865293807667212101531000000000000)
      constant := (15203171193795837863322924995762966088980288929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169461272625994021673/50000000000000000000)
  centralHi := (338922545251988043347/100000000000000000000)
  directionLo := (171293339627936213341/50000000000000000000)
  directionHi := (342586679255872426683/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree048.table
  base := (-3514548807941791751211985900287166296003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-85188521006450310474768572859788589500000000000)
      constant := (1036845066077331325934115400244268752513057507517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree048.table
  base := (-7029478260951836639592549190232287201721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (856980)
      previous := (428490)
      next := (428490)
      square := (2913411968781119752991415323760000000000000)
      linear := (-144701006751343291713606322500579000000000000)
      constant := (1763254602349843573608766890668456080632606319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171293339627936213341/50000000000000000000)
  centralHi := (342586679255872426683/100000000000000000000)
  directionLo := (2704781531879365517/781250000000000000)
  directionHi := (346212036080558786177/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree049.table
  base := (-7008652141459051636337579569046693620639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-1565310735148063816086733031726784291000000000000)
      constant := (19464208332650417285719766024297692531449709082089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree049.table
  base := (-1752245123387723469759417365931610218997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-664708229540156978518623296454445500000000000)
      constant := (8275174998594800264585891726787452367452395094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2704781531879365517/781250000000000000)
  centralHi := (346212036080558786177/100000000000000000000)
  directionLo := (349799821398648325063/100000000000000000000)
  directionHi := (43724977674831040633/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree050.table
  base := (-6966748857431284143838441479797487988669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-1597228092180022043627631751977373971000000000000)
      constant := (20282768929627229277174174422132610925108210566619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree050.table
  base := (-174175799564552872289528650701354711637/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42849000000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (2622070771903007777692273791384000000000000)
      linear := (-135652385739853828865203628331257100000000000)
      constant := (1724633975295358287596848017060745607844264748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349799821398648325063/100000000000000000000)
  centralHi := (43724977674831040633/12500000000000000000)
  directionLo := (353351179669753465149/100000000000000000000)
  directionHi := (7067023593395069303/2000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree051.table
  base := (-690353006029362844750764941310462978879/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5612161000000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (343426528631098882883176946330776000000000000)
      linear := (-18101616102355336346317005246977373900000000000)
      constant := (234654286588943624785524014324559792427991452481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree051.table
  base := (-6903774090374062333614637660292442993043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (856980)
      previous := (428490)
      next := (428490)
      square := (2913411968781119752991415323760000000000000)
      linear := (-153736806190751402251869552635139000000000000)
      constant := (1995250514578458069067251775574976678910122277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353351179669753465149/100000000000000000000)
  centralHi := (7067023593395069303/2000000000000000000)
  directionLo := (356867198405074100247/100000000000000000000)
  directionHi := (44608399800634262531/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree052.table
  base := (-6819116004825413563204283224137328307983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-1661062806243938498709429192478553331000000000000)
      constant := (21972552848780864621107972240399407148831676368633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree052.table
  base := (-3409663128687951871900430704555080047949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-705369327017493475940807832059965500000000000)
      constant := (9341544757021706693108991059729245375025433299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356867198405074100247/100000000000000000000)
  centralHi := (44608399800634262531/12500000000000000000)
  directionLo := (72069782411484121347/20000000000000000000)
  directionHi := (22521807003588787921/6250000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree053.table
  base := (-6713608318308372058864204825293565525497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-1692980163275896726250327912729143011000000000000)
      constant := (22843764963817040768634811823164380077561751078847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree053.table
  base := (-671378940166762879975151149385452563781/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42849000000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (2622070771903007777692273791384000000000000)
      linear := (-143784605235321128349640535452361100000000000)
      constant := (1942384007722664569211064510285375043094547931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72069782411484121347/20000000000000000000)
  centralHi := (22521807003588787921/6250000000000000000)
  directionLo := (45474663197015334351/12500000000000000000)
  directionHi := (363797305576122674809/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree054.table
  base := (-1646773221472575768791191790383192652421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-95827640017103052988401479609985149500000000000)
      constant := (1318473211116775669728855191859826222781192616438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree054.table
  base := (-4117030494560953305327722430980351411/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 529000000000000000000000000000000000000000
      center := (9522)
      previous := (4761)
      next := (4761)
      square := (32371244097567997255460170264000000000000)
      linear := (-1808584507001772364334808697441100000000000)
      constant := (24912966255685454883821748926417223056572960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45474663197015334351/12500000000000000000)
  centralHi := (363797305576122674809/100000000000000000000)
  directionLo := (183606658830723583667/50000000000000000000)
  directionHi := (73442663532289433467/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree055.table
  base := (-1287928457802729471890995997415477378747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (6181677515359779891897185033953968000000000000)
      linear := (-351362975467962636266425070646064474200000000000)
      constant := (4927761538317392634639594087591096382027524719597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree055.table
  base := (-3219888235598538490978641006470793849499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-746030424494829973362992367665485500000000000)
      constant := (10475037098312931264716707532086685454342817349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183606658830723583667/50000000000000000000)
  centralHi := (73442663532289433467/20000000000000000000)
  directionLo := (370597843748998402079/100000000000000000000)
  directionHi := (2316236523431240013/625000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree056.table
  base := (-6271317866137863954218006918284010966253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-1788732234371771408873024073480912051000000000000)
      constant := (25562631540100254337796650590561190696584603375403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree056.table
  base := (-391964582109139578901892252491671042787/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-759584123653942139170387212867325500000000000)
      constant := (10867776028733984730819220188264583099900958696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370597843748998402079/100000000000000000000)
  centralHi := (2316236523431240013/625000000000000000)
  directionLo := (186975869375493987763/50000000000000000000)
  directionHi := (373951738750987975527/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree057.table
  base := (-6082171454261166841838178198844189630747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-202294399044858848490435865970166859000000000000)
      constant := (2944887414153735327409011742716789179377717285733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree057.table
  base := (-1520567687837668695126267865700975984989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (428490)
      previous := (214245)
      next := (214245)
      square := (1456705984390559876495707661880000000000000)
      linear := (-85904202534783811664198006452129500000000000)
      constant := (1251996335878021569017487380502606806670934742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186975869375493987763/50000000000000000000)
  centralHi := (373951738750987975527/100000000000000000000)
  directionLo := (188637909789076655911/50000000000000000000)
  directionHi := (377275819578153311823/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree058.table
  base := (-367015428792803538809111065022539520623/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-926283474217843931977410756991045705500000000000)
      constant := (13731435520377201564815574979946607201360865066184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree058.table
  base := (-5872332240342406236504972176379300404987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-1573383043944332941570353806542011000000000000)
      constant := (23351218299574748802058259233145801356946712037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188637909789076655911/50000000000000000000)
  centralHi := (377275819578153311823/100000000000000000000)
  directionLo := (1902854337317017401/500000000000000000)
  directionHi := (380570867463403480201/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree059.table
  base := (-5641581106804882591227438411074411121853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-1884484305467646091495720234232681091000000000000)
      constant := (28439282610282299276687675611977537012735733111003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree059.table
  base := (-5641654497868166088976161468660274637453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-1600490442262557273185143496945691000000000000)
      constant := (24181403245486030544658654121115404892059776403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1902854337317017401/500000000000000000)
  centralHi := (380570867463403480201/100000000000000000000)
  directionLo := (191918815052959011311/50000000000000000000)
  directionHi := (383837630105918022623/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree060.table
  base := (-5390205479242962472037911401396498896319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-212933518055511591004068772720363419000000000000)
      constant := (3270357761744142483823615292068240113357535464641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree060.table
  base := (-5390268546969116861168038458417818218571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (856980)
      previous := (428490)
      next := (428490)
      square := (2913411968781119752991415323760000000000000)
      linear := (-180844204508975733866659243038819000000000000)
      constant := (2780720839359104744128582667790612767461383469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191918815052959011311/50000000000000000000)
  centralHi := (383837630105918022623/100000000000000000000)
  directionLo := (19353841182618482561/5000000000000000000)
  directionHi := (387076823652369651221/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree061.table
  base := (-639768302269977236473320216134780856083/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-974159509765781273288758837366930225500000000000)
      constant := (15222340720760701420956198100479988078643997486932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree061.table
  base := (-2559100299798090744120338070105403392847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-827352619449502968207361438876525500000000000)
      constant := (12943235051328300081352677466201139070019898897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19353841182618482561/5000000000000000000)
  centralHi := (387076823652369651221/100000000000000000000)
  directionLo := (390289134530142667343/100000000000000000000)
  directionHi := (24393070908133916709/6250000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree062.table
  base := (-1206356566992640976284146730572385698201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-990118188281760387059208197492225065500000000000)
      constant := (15736833119575282525252304170644479706036774397502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree062.table
  base := (-4825472802692849413894636394298110329099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-1681812637217230268029512568156731000000000000)
      constant := (26761349941785621362129861511968482270508436949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390289134530142667343/100000000000000000000)
  centralHi := (24393070908133916709/6250000000000000000)
  directionLo := (393475221145840299583/100000000000000000000)
  directionHi := (6148050330403754681/1562500000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree063.table
  base := (-4512063911775784124004042365493135599327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-223572637066164333517701679470559979000000000000)
      constant := (3613352588312195898930318250875379353121745384353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree063.table
  base := (-2256051934290006655247118644116981803097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (47610)
      previous := (23805)
      next := (23805)
      square := (161856220487839986277300851320000000000000)
      linear := (-10548889108243546911384581842965500000000000)
      constant := (170685964628486224477238426444058616626161687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393475221145840299583/100000000000000000000)
  centralHi := (6148050330403754681/1562500000000000000)
  directionLo := (396635715460985758579/100000000000000000000)
  directionHi := (19831785773049287929/5000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree064.table
  base := (-4178075307520421580684549794627695843987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-2044071090627437229200213835485629491000000000000)
      constant := (33584201802471990716619522891733654706780626666837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree064.table
  base := (-835621921516898658521466590829298672889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (5244141543806015555384547582768000000000000)
      linear := (-347205486770735786251818389792818200000000000)
      constant := (5711159681857469451432905533320352181165379239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396635715460985758579/100000000000000000000)
  centralHi := (19831785773049287929/5000000000000000000)
  directionLo := (199885612227799042893/50000000000000000000)
  directionHi := (399771224455598085787/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree065.table
  base := (-3823473941102590430950455295485570063743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-2075988447659395456741112555736219171000000000000)
      constant := (34665751080971964913097422872624002846129446192393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree065.table
  base := (-3823503378070640887932722979495944382379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-1763134832171903262873881639367771000000000000)
      constant := (29475365787810803939075203396438193279159442229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199885612227799042893/50000000000000000000)
  centralHi := (399771224455598085787/100000000000000000000)
  directionLo := (402882331489243038649/100000000000000000000)
  directionHi := (8057646629784860773/2000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree066.table
  base := (-1724135604648277279535711069665441690889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-117105878038408538015667293110378269500000000000)
      constant := (1986934475259160957423972430072353894594618698871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree066.table
  base := (-1724148233341801842043124127457833644543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (428490)
      previous := (214245)
      next := (214245)
      square := (1456705984390559876495707661880000000000000)
      linear := (-99457901693895977471592851653969500000000000)
      constant := (1689434884542426693447938950395780254018330777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402882331489243038649/100000000000000000000)
  centralHi := (8057646629784860773/2000000000000000000)
  directionLo := (101492399392050671679/25000000000000000000)
  directionHi := (405969597568202686717/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree067.table
  base := (-1526238371680742500713298117417170687297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1069911580861655955911454998118699265500000000000)
      constant := (18440704868540596886488747941415597407695677230647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree067.table
  base := (-610499681925313386104249206909638399679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (5244141543806015555384547582768000000000000)
      linear := (-363469925761670385220692204035026200000000000)
      constant := (6271836880505841320274758950131312304212154529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101492399392050671679/25000000000000000000)
  centralHi := (405969597568202686717/100000000000000000000)
  directionLo := (2556459765790994649/625000000000000000)
  directionHi := (409033562526559143841/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree068.table
  base := (-527219736504725347023917587065921073297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (6181677515359779891897185033953968000000000000)
      linear := (-434348103751054027872761743297597642200000000000)
      constant := (7603103643422604322200575664470579687510279916647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree068.table
  base := (-2636117264116039248520245814971754027257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-1844457027126576257718250710578811000000000000)
      constant := (32323434884863712119094549220636863311686064807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2556459765790994649/625000000000000000)
  centralHi := (409033562526559143841/100000000000000000000)
  directionLo := (51509343266029279517/12500000000000000000)
  directionHi := (412074746128234236137/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree069.table
  base := (-27489298813704593554548617752125985011/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (190962)
      previous := (95481)
      next := (95481)
      square := (649199487015309797510731467544000000000000)
      linear := (-46285609657366695377120509068233100000000000)
      constant := (822666365203540463861253173945022713400146408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree069.table
  base := (-2199159837741251225081253124145963351231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1620)
      previous := (810)
      next := (810)
      square := (5507395026051266073707779440000000000000)
      linear := (-393103218955009575579298550931000000000000)
      constant := (6994870631604454125982542948581686329838921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51509343266029279517/12500000000000000000)
  centralHi := (412074746128234236137/100000000000000000000)
  directionLo := (207546824548178057927/50000000000000000000)
  directionHi := (83018729819271223171/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree070.table
  base := (-1741618223800002978547273476458195719079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-2235575232819186594445606156989167571000000000000)
      constant := (40336291734166514064863222239526355407695160922529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree070.table
  base := (-43540797056390756858488325544392303519/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42849000000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (2622070771903007777692273791384000000000000)
      linear := (-189867182376302492094783009138617100000000000)
      constant := (3429661673268760591423052605079490336746057476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207546824548178057927/50000000000000000000)
  centralHi := (83018729819271223171/20000000000000000000)
  directionLo := (418090754075725707583/100000000000000000000)
  directionHi := (6532668032433214181/1562500000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree071.table
  base := (-315881637706647290366301558146681159719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1133746294925572410993252438619878625500000000000)
      constant := (20761478114739382612195735121760544256137824630338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree071.table
  base := (-252707651463200671463728697762868101147/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (5244141543806015555384547582768000000000000)
      linear := (-385155844416249850512523956357970200000000000)
      constant := (7061109528697735240384913600500695064733952197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418090754075725707583/100000000000000000000)
  centralHi := (6532668032433214181/1562500000000000000)
  directionLo := (84213305306724324121/20000000000000000000)
  directionHi := (210533263266810810303/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree072.table
  base := (-30594921493452232660967188017614860017/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (686853057262197765766353892661552000000000000)
      linear := (-51097998819624512211720079944229931800000000000)
      constant := (949491976080100034920404585976967394447960666315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree072.table
  base := (-764883068829849448876863102209659273621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (95220)
      previous := (47610)
      next := (47610)
      square := (323712440975679972554601702640000000000000)
      linear := (-24109711362956464002190240397451000000000000)
      constant := (448510760907876387534460622896043090244254491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84213305306724324121/20000000000000000000)
  centralHi := (210533263266810810303/50000000000000000000)
  directionLo := (424021415603704158179/100000000000000000000)
  directionHi := (21201070780185207909/5000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree073.table
  base := (-245661191345841310238580496192831605077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-2331327303915061277068302317740936611000000000000)
      constant := (43948839639355733093746078897297780283377775127427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree073.table
  base := (-245669785848232394775439893031355788111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-1979994018717697915792199162597211000000000000)
      constant := (37368088554190170444603729690139642435835231761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424021415603704158179/100000000000000000000)
  centralHi := (21201070780185207909/5000000000000000000)
  directionLo := (42695585487735068187/10000000000000000000)
  directionHi := (426955854877350681871/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree074.table
  base := (294106022644164554082227621781930477943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-2363244660947019504609201037991526291000000000000)
      constant := (45188058226997165914762463488547793025597207583407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree074.table
  base := (11763946426743063739489755605021119419/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (5244141543806015555384547582768000000000000)
      linear := (-401420283407184449481397770600178200000000000)
      constant := (7684339655971301740744066305642776549729923655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42695585487735068187/10000000000000000000)
  centralHi := (426955854877350681871/100000000000000000000)
  directionLo := (429870263146370086211/100000000000000000000)
  directionHi := (107467565786592521553/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree075.table
  base := (213606524863507539772461075396182839979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-133064556554387651786116653235673109500000000000)
      constant := (2580266364444086370554425755550429840016798769238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree075.table
  base := (427209897200854040896681205907812030363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (428490)
      previous := (214245)
      next := (214245)
      square := (1456705984390559876495707661880000000000000)
      linear := (-113011600853008143278987696855809500000000000)
      constant := (2193900039134956385069922291643289593076558243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429870263146370086211/100000000000000000000)
  centralHi := (107467565786592521553/25000000000000000000)
  directionLo := (2704781531879365517/625000000000000000)
  directionHi := (432765045100698482721/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree076.table
  base := (358824230517961575580915602922435832293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1213539687505467979845499239246352825500000000000)
      constant := (23859524265707897149571682260479386240253951673114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree076.table
  base := (89705720197836256062159759209836295487/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1030658106836185455318284116904125500000000000)
      constant := (20286797869130110277725552398481276203402579704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2704781531879365517/625000000000000000)
  centralHi := (432765045100698482721/100000000000000000000)
  directionLo := (108910147996091748411/25000000000000000000)
  directionHi := (87128118396873398729/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree077.table
  base := (254589587690252728144980235760671787233/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1229498366021447093615948599371647665500000000000)
      constant := (24505410025451856709191102245851264981121936258468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree077.table
  base := (203671207933282887655995469564032847681/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42849000000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (2622070771903007777692273791384000000000000)
      linear := (-208842361199059524225135792421193100000000000)
      constant := (4167188330560848637583715690454671943490283169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108910147996091748411/25000000000000000000)
  centralHi := (87128118396873398729/20000000000000000000)
  directionLo := (438497282212751972723/100000000000000000000)
  directionHi := (109624320553187993181/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree078.table
  base := (265868392604830759223727561367723144313/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5612161000000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (343426528631098882883176946330776000000000000)
      linear := (-27676823211942804608586621322154277900000000000)
      constant := (559112322689992631795137417510307222189310790393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree078.table
  base := (166167498093803734523503447795445608749/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (428490)
      previous := (214245)
      next := (214245)
      square := (1456705984390559876495707661880000000000000)
      linear := (-117529500572712198548119311923089500000000000)
      constant := (2376947963471287716893486782606393932346031912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438497282212751972723/100000000000000000000)
  centralHi := (109624320553187993181/25000000000000000000)
  directionLo := (88267096390772926681/20000000000000000000)
  directionHi := (220667740976932316703/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree079.table
  base := (3301197318168495459853995547633684525949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-2522831446106810642313694639244474691000000000000)
      constant := (51646915440477742188042154547373060745745510192101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree079.table
  base := (660238786392068001413173302199492005291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (5244141543806015555384547582768000000000000)
      linear := (-428527681725408781096187461003858200000000000)
      constant := (8782627158964264702476206730967915832934714059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88267096390772926681/20000000000000000000)
  centralHi := (220667740976932316703/50000000000000000000)
  directionLo := (444155545676208013939/100000000000000000000)
  directionHi := (22207777283810400697/5000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree080.table
  base := (3964255798381476021019671715611155160269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-2554748803138768869854593359495064371000000000000)
      constant := (52991239191513923166785767090807502825398693881781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree080.table
  base := (1982126450381063160480008663229239202397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1084872903472634118547863497711485500000000000)
      constant := (22528050308474032679313729356429549670583509053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444155545676208013939/100000000000000000000)
  centralHi := (22207777283810400697/5000000000000000000)
  directionLo := (446957816665521838457/100000000000000000000)
  directionHi := (223478908332760919229/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree081.table
  base := (4647858454496208500427614080637524136161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-287407351130080788599499119971739339000000000000)
      constant := (6039231138792623660610659054049969429593521453921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree081.table
  base := (929571195071127493701493190210201462397/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (19044)
      previous := (9522)
      next := (9522)
      square := (64742488195135994510920340528000000000000)
      linear := (-5424328901885166836322263421794200000000000)
      constant := (114108537704384475525650372041683396573608013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446957816665521838457/100000000000000000000)
  centralHi := (223478908332760919229/50000000000000000000)
  directionLo := (44974262751254784651/10000000000000000000)
  directionHi := (449742627512547846511/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree082.table
  base := (5352004515711770353129849091848358813959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-2618583517202685324936390799996243731000000000000)
      constant := (55732438574404081637735647856578990902247362598591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree082.table
  base := (5352002394935890911970396708664229783067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-2223960603581716900325306376230331000000000000)
      constant := (47386707222204532503404331883001935581974637883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44974262751254784651/10000000000000000000)
  centralHi := (449742627512547846511/100000000000000000000)
  directionLo := (181004120229511013/40000000000000000)
  directionHi := (452510300573777532501/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree083.table
  base := (3038346665356272236561200742196948039531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1325250437117321776238644760123416705500000000000)
      constant := (28564657067213868149192840409379055165208341028419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree083.table
  base := (6076691516768834059927753114519466588723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-2251068001899941231940096066634011000000000000)
      constant := (48574348945194013685685451481903297623860191827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181004120229511013/40000000000000000)
  centralHi := (452510300573777532501/100000000000000000000)
  directionLo := (455261148406989167/100000000000000000)
  directionHi := (455261148406989167001/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree084.table
  base := (1705481087289149523030634786380354447001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-149023235070366765556566013360967949500000000000)
      constant := (3252428161189283841206945827653185415787271158322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree084.table
  base := (1705480699469507840958712284738357372279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (428490)
      previous := (214245)
      next := (214245)
      square := (1456705984390559876495707661880000000000000)
      linear := (-126565300012120309086382542057649500000000000)
      constant := (2765382384221008824884009345661156638898840638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455261148406989167/100000000000000000)
  centralHi := (455261148406989167001/100000000000000000000)
  directionLo := (228997737091619937497/50000000000000000000)
  directionHi := (91599094836647974999/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree085.table
  base := (118557767281744467083310576525862771483/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1357167794149280003779543480374006385500000000000)
      constant := (29987808425927342929085701607083778134541015771744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree085.table
  base := (7587695779571439801280146988560262489347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-2305282798536389895169675447441371000000000000)
      constant := (50994309114902472638617170120084853687406029603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228997737091619937497/50000000000000000000)
  centralHi := (91599094836647974999/20000000000000000000)
  directionLo := (460713572076850011623/100000000000000000000)
  directionHi := (57589196509606251453/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree086.table
  base := (65421962565893794630271000246423251801/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1373126472665259117549992840499301225500000000000)
      constant := (30712521982962569077662911608814904231332433129536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree086.table
  base := (8374010074367840572588083549172555802083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-2332390196854614226784465137845051000000000000)
      constant := (52226627525363772313453158972576440843563454467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460713572076850011623/100000000000000000000)
  centralHi := (57589196509606251453/12500000000000000000)
  directionLo := (463415727634799851343/100000000000000000000)
  directionHi := (28963482977174990709/6250000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree087.table
  base := (9180866324397959919836994764854181571717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-308685589151386273626764933472132459000000000000)
      constant := (6987998691872333326383637799262273239003708850437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree087.table
  base := (73446922839606357583841646285040122199/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9522000000000000000000000000000000000000000
      center := (171396)
      previous := (85698)
      next := (85698)
      square := (582682393756223950598283064752000000000000)
      linear := (-52433279892729745742205662849971800000000000)
      constant := (1188307514074152795079457952117155500544735975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463415727634799851343/100000000000000000000)
  centralHi := (28963482977174990709/6250000000000000000)
  directionLo := (466102218126851576683/100000000000000000000)
  directionHi := (116525554531712894171/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree088.table
  base := (1251032771681235324094244417131458804553/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1405043829697217345090891560749890905500000000000)
      constant := (32188224810232881755767671020881232533136682885188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree088.table
  base := (1251032668104462319060327205410909592741/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1193302496745531445007022259326205500000000000)
      constant := (27367970463487347126629005133063012260557436436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466102218126851576683/100000000000000000000)
  centralHi := (116525554531712894171/25000000000000000000)
  directionLo := (29298332054850732791/6250000000000000000)
  directionHi := (468773312877611724657/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree089.table
  base := (1357024814829129096367524365471610456217/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1421002508213196458861340920875185745500000000000)
      constant := (32939214067400427125522090853949420987894637177732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree089.table
  base := (10856197810484274674704809381023614531993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-2413712391809287221628834209056091000000000000)
      constant := (56012935896270346086557244283241239859081368057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29298332054850732791/6250000000000000000)
  centralHi := (468773312877611724657/100000000000000000000)
  directionLo := (235714636790829868003/50000000000000000000)
  directionHi := (471429273581659736007/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree090.table
  base := (2344935031952488506504296934442378940297/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (686853057262197765766353892661552000000000000)
      linear := (-63864941632407803228079568044465803800000000000)
      constant := (1497731639105445327292504818780321342835956151817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree090.table
  base := (2931168638660507798004693438058750278989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (47610)
      previous := (23805)
      next := (23805)
      square := (161856220487839986277300851320000000000000)
      linear := (-15066788827947602180516196910245500000000000)
      constant := (353733475510936256519895508729061157795170362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235714636790829868003/50000000000000000000)
  centralHi := (471429273581659736007/100000000000000000000)
  directionLo := (47407035460278626263/10000000000000000000)
  directionHi := (474070354602786262631/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree091.table
  base := (1261369192772682442158945495567476467737/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (3090838757679889945948592516976984000000000000)
      linear := (-290583973049030937280447928225155085100000000000)
      constant := (6893493648675660199381240390907667387555862146913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree091.table
  base := (1261369141070903247319797654896608048321/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42849000000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (2622070771903007777692273791384000000000000)
      linear := (-246792718844573588485841358986345100000000000)
      constant := (5861160232934003602039306889444934858262506529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47407035460278626263/10000000000000000000)
  centralHi := (474070354602786262631/100000000000000000000)
  directionLo := (238348401629154856641/50000000000000000000)
  directionHi := (476696803258309713283/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree092.table
  base := (13523248679672882262080885428476187055291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17186580)
      previous := (8593290)
      next := (8593290)
      square := (58427953831377881775965832078960000000000000)
      linear := (-5553416044465534216153833653123139000000000000)
      constant := (133250408900983175369199400096331432816226239971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree092.table
  base := (13523248237983734873310747842824432502609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (14580)
      previous := (7290)
      next := (7290)
      square := (49566555234461394663370014960000000000000)
      linear := (-4716511506170057119987151758539000000000000)
      constant := (113295413572677718403450957655016779032711329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238348401629154856641/50000000000000000000)
  centralHi := (476696803258309713283/100000000000000000000)
  directionLo := (239654430044685260961/50000000000000000000)
  directionHi := (479308860089370521923/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree093.table
  base := (225833520233369917139284240313945824399/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-164981913586345879327015373486262789500000000000)
      constant := (4003417401068934075337858332165947204127757319648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree093.table
  base := (1445334491764449176323425846383398064819/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4761000000000000000000000000000000000000000
      center := (85698)
      previous := (42849)
      next := (42849)
      square := (291341196878111975299141532376000000000000)
      linear := (-28023799834246494978755477451897900000000000)
      constant := (680775970883330176276769460246302058186603259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239654430044685260961/50000000000000000000)
  centralHi := (479308860089370521923/100000000000000000000)
  directionLo := (60238344889754904699/12500000000000000000)
  directionHi := (481906759118039237593/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree094.table
  base := (7701990835799731759103236559565116520767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1500795900793092027713587721501659945500000000000)
      constant := (36825538606735517484914446586612639909584738227383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree094.table
  base := (1925497668669291089535163562048827791267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1274624691700204439851391330537245500000000000)
      constant := (31310646561850152745817516766627777888111998732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60238344889754904699/12500000000000000000)
  centralHi := (481906759118039237593/100000000000000000000)
  directionLo := (121122682023004061943/25000000000000000000)
  directionHi := (484490728092016247773/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree095.table
  base := (2046894715448922550985986686493218371581/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1516754579309071141484037081626954785500000000000)
      constant := (37629079143481635729476774007761877399990934275476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree095.table
  base := (8187578724196165177956537574162453425311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1288178390859316605658786175739085500000000000)
      constant := (31993820504459037706316795457473659466821151039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121122682023004061943/25000000000000000000)
  centralHi := (484490728092016247773/100000000000000000000)
  directionLo := (487060988717647299157/100000000000000000000)
  directionHi := (243530494358823649579/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree096.table
  base := (3473374675645074866852994979335881800089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (202037796)
      previous := (101018898)
      next := (101018898)
      square := (686853057262197765766353892661552000000000000)
      linear := (-68120589236668900233532730744544427800000000000)
      constant := (1708505698578804231907971009229304478539069282329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree096.table
  base := (67839348215742069838329509784545694219/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (428490)
      previous := (214245)
      next := (214245)
      square := (1456705984390559876495707661880000000000000)
      linear := (-144636898890936530162909002326769500000000000)
      constant := (3631604501782672210161167494260972422422612352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487060988717647299157/100000000000000000000)
  centralHi := (243530494358823649579/50000000000000000000)
  directionLo := (244808878440964778223/50000000000000000000)
  directionHi := (489617756881929556447/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree097.table
  base := (9189564287063343534703797232926600558551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1548671936341029369024935801877544465500000000000)
      constant := (39262435828809893339971684228035752656405503248399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree097.table
  base := (18379128373483377281291152303236102308893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-2630571578355081874547151732285531000000000000)
      constant := (66765013190622990156674988012343210747833756157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244808878440964778223/50000000000000000000)
  centralHi := (489617756881929556447/100000000000000000000)
  directionLo := (492161242864137368091/100000000000000000000)
  directionHi := (123040310716034342023/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree098.table
  base := (4852980814869477273356563991029018878081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1564630614857008482795385162002839305500000000000)
      constant := (40092251974533395693875297071023505194584938974738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree098.table
  base := (4852980772045810827828005236882518359789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1328839488336653103080970711344605500000000000)
      constant := (34088018741169381300894624134922317058397197722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492161242864137368091/100000000000000000000)
  centralHi := (123040310716034342023/25000000000000000000)
  directionLo := (494691651537654851209/100000000000000000000)
  directionHi := (49469165153765485121/10000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree099.table
  base := (5116314347634199824381800734366150184861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-175621032596998621840648280236459349500000000000)
      constant := (4547869628232100447936113932228517199825239389242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree099.table
  base := (2046525724431309768852964814052732947037/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 529000000000000000000000000000000000000000
      center := (9522)
      previous := (4761)
      next := (4761)
      square := (32371244097567997255460170264000000000000)
      linear := (-3314551080236457454045347053201100000000000)
      constant := (85928338154805190596555369361208795728982573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494691651537654851209/100000000000000000000)
  centralHi := (49469165153765485121/10000000000000000000)
  directionLo := (248604591281281780959/50000000000000000000)
  directionHi := (497209182562563561919/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree100.table
  base := (107695654651918843170864428609470025957/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (3090838757679889945948592516976984000000000000)
      linear := (-319309594377793342067256776450685797100000000000)
      constant := (8355631973308804860514418192993138678862075353860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree100.table
  base := (1346195675348396222584726405003158193251/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1355946886654877434695760401748285500000000000)
      constant := (35521381229113978376523539455187392603380896792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248604591281281780959/50000000000000000000)
  centralHi := (497209182562563561919/100000000000000000000)
  directionLo := (499714030569497607233/100000000000000000000)
  directionHi := (249857015284748803617/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree101.table
  base := (2829192980982931159895788416056864416713/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1612506650404945824106733242378723825500000000000)
      constant := (42634251611111936276220234203067375009173520084548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree101.table
  base := (176824560479241038163934020963859959001/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1369500585813989600503155246950125500000000000)
      constant := (36249231569766903481448514239428053364526966336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499714030569497607233/100000000000000000000)
  centralHi := (249857015284748803617/50000000000000000000)
  directionLo := (251103192667622665667/50000000000000000000)
  directionHi := (100441277067049066267/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree102.table
  base := (11874248058345141060016222362092528309331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-180940592102324993097464733611557629500000000000)
      constant := (4833233543014311710961714876059231442269023374291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree102.table
  base := (5937124006446873290969608682878653361847/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (428490)
      previous := (214245)
      next := (214245)
      square := (1456705984390559876495707661880000000000000)
      linear := (-153672698330344640701172232461329500000000000)
      constant := (4109391997122384239015028791317759537311507134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251103192667622665667/50000000000000000000)
  centralHi := (100441277067049066267/20000000000000000000)
  directionLo := (504686431950545946989/100000000000000000000)
  directionHi := (50468643195054594699/10000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree103.table
  base := (24883987714692712940938790947732529074439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (856980)
      previous := (428490)
      next := (428490)
      square := (2913411968781119752991415323760000000000000)
      linear := (-310005468458272042915945322392179000000000000)
      constant := (8365107115474539575156947216120189070923404079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree103.table
  base := (4976797527425068001501082359204165125563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (5244141543806015555384547582768000000000000)
      linear := (-558643193652885572847177974941522200000000000)
      constant := (15090908176660381683070704076363433871465248987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504686431950545946989/100000000000000000000)
  centralHi := (50468643195054594699/10000000000000000000)
  directionLo := (507154350980500977471/100000000000000000000)
  directionHi := (7924286734070327773/1562500000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree104.table
  base := (52080037246349047544970903414728460491/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (3090838757679889945948592516976984000000000000)
      linear := (-332076537190576633083616264550921669100000000000)
      constant := (9051015606271487555100973662505982543600933972950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree104.table
  base := (104160074227970013447250463266546511921/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42849000000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (2622070771903007777692273791384000000000000)
      linear := (-282032336658265219585067956511129100000000000)
      constant := (7695491794404390897721996631293668687232573225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507154350980500977471/100000000000000000000)
  centralHi := (7924286734070327773/1562500000000000000)
  directionLo := (509610318617993939713/100000000000000000000)
  directionHi := (254805159308996969857/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree105.table
  base := (13608294413187576133931413368119560721401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-186260151607651364354281186986655909500000000000)
      constant := (5127355988744333837319578821077777270767778557561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree105.table
  base := (27216588769912560914459850444135425325121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (856980)
      previous := (428490)
      next := (428490)
      square := (2913411968781119752991415323760000000000000)
      linear := (-316381196100097391940607695057219000000000000)
      constant := (8718909681085085418689821218190023759972901081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509610318617993939713/100000000000000000000)
  centralHi := (254805159308996969857/50000000000000000000)
  directionLo := (512054506830487166791/100000000000000000000)
  directionHi := (64006813353810895849/12500000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree106.table
  base := (14206849155506831548852652609561719270197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1692300042984841392958980043005198025500000000000)
      constant := (47046088295723989094688604478506841967330332591453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree106.table
  base := (443964035356991932186438231273265145637/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1437269081609550429540129472959325500000000000)
      constant := (40000174219954410641730739573912983423212794016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512054506830487166791/100000000000000000000)
  centralHi := (64006813353810895849/12500000000000000000)
  directionLo := (514487083500541883567/100000000000000000000)
  directionHi := (32155442718783867723/6250000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree107.table
  base := (29631347065903411038086739859717621828903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-3416517443001641013458858806260985731000000000000)
      constant := (95909462444299751617465115841271974118668262804447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree107.table
  base := (29631347024818255062550432088915303719131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-2901645561537325190695048636322331000000000000)
      constant := (81545401874002626643441931129586088849061044219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514487083500541883567/100000000000000000000)
  centralHi := (32155442718783867723/6250000000000000000)
  directionLo := (516908212560386473429/100000000000000000000)
  directionHi := (51690821256038647343/10000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree108.table
  base := (7717383770406610777540221711659002221769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-191579711112977735611097640361754189500000000000)
      constant := (5430236964193201874463705944530117316135850665618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree108.table
  base := (30869535046584373513992161004475318794561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (95220)
      previous := (47610)
      next := (47610)
      square := (323712440975679972554601702640000000000000)
      linear := (-36157443948833944719874547243531000000000000)
      constant := (1025991943600632575243638534699355443642322769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516908212560386473429/100000000000000000000)
  centralHi := (51690821256038647343/10000000000000000000)
  directionLo := (103863610824167635853/20000000000000000000)
  directionHi := (259659027060419089633/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree109.table
  base := (32128262350258383818622792402103414109653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-3480352157065557468540656246762165091000000000000)
      constant := (99596585324581368718085027135538203579197398611197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree109.table
  base := (16064131160186552162318275804717539009561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1477930179086886926962314008564845500000000000)
      constant := (42340092556260801614312146545309131329020679289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103863610824167635853/20000000000000000000)
  centralHi := (259659027060419089633/50000000000000000000)
  directionLo := (104343352918973030309/20000000000000000000)
  directionHi := (260858382297432575773/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree110.table
  base := (16703764432567990701259494495733920150883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1756134757048757848040777483506377385500000000000)
      constant := (50733211175637199687843018441722794499931097193467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree110.table
  base := (16703764419825382017039590287975018584709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1491483878245999092769708853766685500000000000)
      constant := (43134957458166879371257888667161346571336195941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104343352918973030309/20000000000000000000)
  centralHi := (260858382297432575773/50000000000000000000)
  directionLo := (8189132762750916949/1562500000000000000)
  directionHi := (524104496816058684737/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree111.table
  base := (17353667310330352383551460960289850572201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-196899270618304106867914093736852469500000000000)
      constant := (5741876468626330388463595609611911601327134136361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree111.table
  base := (34707334598929516694681630860337478131601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (856980)
      previous := (428490)
      next := (428490)
      square := (2913411968781119752991415323760000000000000)
      linear := (-334452794978913613017134155326339000000000000)
      constant := (9763837426983617428209868389984035733384552361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8189132762750916949/1562500000000000000)
  centralHi := (524104496816058684737/100000000000000000000)
  directionLo := (65810175019033696617/12500000000000000000)
  directionHi := (526481400152269572937/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree112.table
  base := (18013839806066402407231955969608717583969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1788052114080716075581676203756967065500000000000)
      constant := (52629323788171314915343681972050119426762885423081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree112.table
  base := (18013839796802086519885703778573370380731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1518591276564223424384498544170365500000000000)
      constant := (44747025445940334903927878941507746347443942619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65810175019033696617/12500000000000000000)
  centralHi := (526481400152269572937/100000000000000000000)
  directionLo := (264423810307323839053/50000000000000000000)
  directionHi := (528847620614647678107/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree113.table
  base := (1494742553424444772372310718572129369467/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (6181677515359779891897185033953968000000000000)
      linear := (-721604317038678075740850225552904762200000000000)
      constant := (21436207154856276391557929570439221155142477968415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree113.table
  base := (7473712763962867575782462750133749385031/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (5244141543806015555384547582768000000000000)
      linear := (-612857990289334236076757355748882200000000000)
      constant := (18225691412650536706180320770431797627399193319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264423810307323839053/50000000000000000000)
  centralHi := (528847620614647678107/100000000000000000000)
  directionLo := (13280082524057748953/2500000000000000000)
  directionHi := (531203300962309958121/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree114.table
  base := (38729987287794631776493327034117438262023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-404437660247260956249461094223901499000000000000)
      constant := (12124549003213718983372474484320704607434033261703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree114.table
  base := (7745997454865594597345414194557751378193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9522000000000000000000000000000000000000000
      center := (171396)
      previous := (85698)
      next := (85698)
      square := (582682393756223950598283064752000000000000)
      linear := (-68697718883664344711079477092179800000000000)
      constant := (2061727896818446853713492498049034654311576873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13280082524057748953/2500000000000000000)
  centralHi := (531203300962309958121/100000000000000000000)
  directionLo := (533548580802849272811/100000000000000000000)
  directionHi := (133387145200712318203/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree115.table
  base := (8022389993184482598904429301845547351657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190962000000000000000000000000000000000000000
      center := (3437316)
      previous := (1718658)
      next := (1718658)
      square := (11685590766275576355193166415792000000000000)
      linear := (-1388225443953613169673364298021059800000000000)
      constant := (41995600506665196028230376624610629206683562017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree115.table
  base := (10027987488610763179454797318106912454947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (7290)
      previous := (3645)
      next := (3645)
      square := (24783277617230697331685007480000000000000)
      linear := (-2947547020872514029880308279349500000000000)
      constant := (89264599028825298080900604314975819817701414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533548580802849272811/100000000000000000000)
  centralHi := (133387145200712318203/25000000000000000000)
  directionLo := (267941798344442102957/50000000000000000000)
  directionHi := (107176719337776841183/20000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree116.table
  base := (10378612966922273993332153783311188737877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1851886828144632530663473644258146425500000000000)
      constant := (56526651353891428537164936396706999540370345399546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree116.table
  base := (20757225928952252475281360309801292326783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1572806073200672087614077924977725500000000000)
      constant := (48060514155078613401509542232067913574910324767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267941798344442102957/50000000000000000000)
  centralHi := (107176719337776841183/20000000000000000000)
  directionLo := (269104241105419423373/50000000000000000000)
  directionHi := (538208482210838846747/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree117.table
  base := (42937492991173476716259927478671644639451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-415076779257913698763094000974098059000000000000)
      constant := (12782862125754074737116257686266213411351385963611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree117.table
  base := (8587498596566813081324323398829458819511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (19044)
      previous := (9522)
      next := (9522)
      square := (64742488195135994510920340528000000000000)
      linear := (-7833875419060662979859124791010200000000000)
      constant := (241518525851184718447712287375962183715521319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269104241105419423373/50000000000000000000)
  centralHi := (538208482210838846747/100000000000000000000)
  directionLo := (540523368086130910103/100000000000000000000)
  directionHi := (67565421010766363763/12500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree118.table
  base := (22190536667389103049308864996671667804643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1883804185176590758204372364508736105500000000000)
      constant := (58527866306030104474834769595956914331223557571707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree118.table
  base := (5547634165958880163228708727369989911781/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1599913471518896419228867615381405500000000000)
      constant := (49761934875574021874784336631655375790919616276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540523368086130910103/100000000000000000000)
  centralHi := (67565421010766363763/12500000000000000000)
  directionLo := (542828382244936683389/100000000000000000000)
  directionHi := (54282838224493668339/10000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree119.table
  base := (45845192897178853440662475856869138632239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-3799525727385139743949643449268061891000000000000)
      constant := (119083223148536569757327192866560087283919005526311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree119.table
  base := (45845192891122291170181484865439713582069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-3226934341356017170072524921166491000000000000)
      constant := (101247628654356515318563621954972715287278074581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542828382244936683389/100000000000000000000)
  centralHi := (54282838224493668339/10000000000000000000)
  directionLo := (272561824956346013889/50000000000000000000)
  directionHi := (545123649912692027779/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree120.table
  base := (23664925838640444381474501506253523321507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-212857949134283220638363453862147309500000000000)
      constant := (6729346152286692830602417985507386169697552046627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree120.table
  base := (47329851672119990234771037772173601195401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (856980)
      previous := (428490)
      next := (428490)
      square := (2913411968781119752991415323760000000000000)
      linear := (-361560193297137944631923845730019000000000000)
      constant := (11442919964367718939439651580487598515291304161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272561824956346013889/50000000000000000000)
  centralHi := (545123649912692027779/100000000000000000000)
  directionLo := (136852323422369995151/25000000000000000000)
  directionHi := (109481858737895996121/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree121.table
  base := (9767009934836671170217577780334545757043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (6181677515359779891897185033953968000000000000)
      linear := (-772672088289811239806288177953848250200000000000)
      constant := (24638151077977281145651319240954031040553529799307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree121.table
  base := (12208762417446493208493864984304323171329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1640574568996232916651052150986925500000000000)
      constant := (52369911412984640319071062887416527387136552642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136852323422369995151/25000000000000000000)
  centralHi := (109481858737895996121/20000000000000000000)
  directionLo := (549685433626447367957/100000000000000000000)
  directionHi := (274842716813223683979/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree122.table
  base := (25180393443574099259269460687397923695279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1947638899240507213286169805009915465500000000000)
      constant := (62635398547338547639126611465726898193092586191271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree122.table
  base := (6295098360425203828126592157588863313323/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1654128268155345082458446996188765500000000000)
      constant := (53254129047152577109619770042070911816450308908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549685433626447367957/100000000000000000000)
  centralHi := (274842716813223683979/50000000000000000000)
  directionLo := (275976093649692600823/50000000000000000000)
  directionHi := (551952187299385201647/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree123.table
  base := (51907063315574363242583803191777850807727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-436355017279219183790359814474491179000000000000)
      constant := (14152039539500242302064599304818697339466943968047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree123.table
  base := (51907063312382503925579948535457091537569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (856980)
      previous := (428490)
      next := (428490)
      square := (2913411968781119752991415323760000000000000)
      linear := (-370595992736546055170187075864579000000000000)
      constant := (12032398387143560853924678809056388212810366009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275976093649692600823/50000000000000000000)
  centralHi := (551952187299385201647/100000000000000000000)
  directionLo := (554209669879600468333/100000000000000000000)
  directionHi := (277104834939800234167/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree124.table
  base := (2673693947948796861302408132147897150143/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (3090838757679889945948592516976984000000000000)
      linear := (-395911251254493088165413705052101029100000000000)
      constant := (12948343167233711886159378236853743942524786402414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree124.table
  base := (13368469739064209321819158925633352619913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1681235666473569414073236686592445500000000000)
      constant := (55044902497954873393590661069781649052821304274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554209669879600468333/100000000000000000000)
  centralHi := (277104834939800234167/50000000000000000000)
  directionLo := (69557249275275023549/12500000000000000000)
  directionHi := (556457994202200188393/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree125.table
  base := (27530616908481847882122336568250083391293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-1995514934788444554597517885385799985500000000000)
      constant := (65808012272581125090959722111762302200048260827557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree125.table
  base := (55061233814647483512261270058623308296991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-3389578731265363159761263063588571000000000000)
      constant := (111902916629142091144536866994900825137217767359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69557249275275023549/12500000000000000000)
  centralHi := (556457994202200188393/100000000000000000000)
  directionLo := (558697270831902298071/100000000000000000000)
  directionHi := (69837158853987787259/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree126.table
  base := (7083640986153691229235377929606522172331/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-223497068144935963151996360612343869500000000000)
      constant := (7431451915220111792364447640043528490824765269164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree126.table
  base := (7083640985907079483313324266125271281137/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (47610)
      previous := (23805)
      next := (23805)
      square := (161856220487839986277300851320000000000000)
      linear := (-21090655120886342539358350333285500000000000)
      constant := (702042718419606913806434628962874074030885892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558697270831902298071/100000000000000000000)
  centralHi := (69837158853987787259/12500000000000000000)
  directionLo := (560927608126481963289/100000000000000000000)
  directionHi := (56092760812648196329/10000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree127.table
  base := (14574390293883326706028195508398138451887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-2027432291820402782138416605636389665500000000000)
      constant := (67966880729362138068827317771655270498911050760526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree127.table
  base := (29148780586926474484639017413380483855557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1721896763950905911495421222197965500000000000)
      constant := (57786908130201260272639427554308328852726761893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560927608126481963289/100000000000000000000)
  centralHi := (56092760812648196329/10000000000000000000)
  directionLo := (22525964491918253653/4000000000000000000)
  directionHi := (281574556148978170663/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree128.table
  base := (14986633418922946657082374687354635080097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-2043390970336381895908865965761684505500000000000)
      constant := (69059452749719893225191943125851087194983540673106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree128.table
  base := (59946533674260677043385115509109870452249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-3470900926220036154605632134799611000000000000)
      constant := (117431604258413162139639367911127096839008417401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22525964491918253653/4000000000000000000)
  centralHi := (281574556148978170663/50000000000000000000)
  directionLo := (282680943735802772119/50000000000000000000)
  directionHi := (565361887471605544239/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree129.table
  base := (30808022694784636938513430003678708018239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-228816627650262334408812813987442149500000000000)
      constant := (7795642588672316072355677463620238988420348204479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree129.table
  base := (30808022694175257918126575371085215025423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (428490)
      previous := (214245)
      next := (214245)
      square := (1456705984390559876495707661880000000000000)
      linear := (-194333795807681138123356768066849500000000000)
      constant := (6628015798777928014544743089075592208736038903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282680943735802772119/50000000000000000000)
  centralHi := (565361887471605544239/100000000000000000000)
  directionLo := (283783017871461301583/50000000000000000000)
  directionHi := (567566035742922603167/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree130.table
  base := (31653048158534868290044928717430527830087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-2075308327368340123449764686012274185500000000000)
      constant := (71270872374352567085401238652084565333976859992063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree130.table
  base := (63306096316031883208685995464003181260661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-3525115722856484817835211515606971000000000000)
      constant := (121191856619167265557694462565558302313838063189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283783017871461301583/50000000000000000000)
  centralHi := (567566035742922603167/100000000000000000000)
  directionLo := (1139523314465161131/200000000000000000)
  directionHi := (569761657232580565501/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree131.table
  base := (16254171614532540816779839911670669971211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-2091267005884319237220214046137569025500000000000)
      constant := (72389719978623469190467097596184619733663426945478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree131.table
  base := (16254171614311603630661514094972748946487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1776111560587354574725000603005325500000000000)
      constant := (61547160490952172580465677981317345139216042926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1139523314465161131/200000000000000000)
  centralHi := (569761657232580565501/100000000000000000000)
  directionLo := (571948850139500458561/100000000000000000000)
  directionHi := (285974425069750229281/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree132.table
  base := (8343476976589370756817850943599175337321/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-234136187155588705665629267362540429500000000000)
      constant := (8168591790095850244911501216578071664841099042724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree132.table
  base := (66747815811962483712781372385089004193927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (856980)
      previous := (428490)
      next := (428490)
      square := (2913411968781119752991415323760000000000000)
      linear := (-397703391054770386784976766268259000000000000)
      constant := (13890186385134731991804643290356956748967286447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571948850139500458561/100000000000000000000)
  centralHi := (285974425069750229281/50000000000000000000)
  directionLo := (114825542158419941267/20000000000000000000)
  directionHi := (17941490962253115823/3125000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree133.table
  base := (68499484380811266932274366805023778535941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-4246368725832554929522225532776317411000000000000)
      constant := (149307381542139581792027305487252082701248406606509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree133.table
  base := (17124871095042647572111953900524533951767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1803218958905578906339790293409005500000000000)
      constant := (63471963036045793383551076640934553010598528366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114825542158419941267/20000000000000000000)
  centralHi := (17941490962253115823/3125000000000000000)
  directionLo := (576298333697796674011/100000000000000000000)
  directionHi := (144074583424449168503/25000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree134.table
  base := (70271692162424929798909319098794906474487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-4278286082864513157063124253026907091000000000000)
      constant := (151597627918490066714082085510739009819032870927663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree134.table
  base := (35135846080939738659896912771927053727757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1816772658064691072147185138610845500000000000)
      constant := (64445533399770858157662618726646979325180659693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576298333697796674011/100000000000000000000)
  centralHi := (144074583424449168503/25000000000000000000)
  directionLo := (289230405795421661693/50000000000000000000)
  directionHi := (578460811590843323387/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree135.table
  base := (36032219578788611049910901446495275114027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-239455746660915076922445720737638709500000000000)
      constant := (8550299519487657410084380405637557620929212882347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree135.table
  base := (14412887831422573283920679672054651810399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (19044)
      previous := (9522)
      next := (9522)
      square := (64742488195135994510920340528000000000000)
      linear := (-9038648677648411051627555475618200000000000)
      constant := (323094073206330846958758576737073910807701071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289230405795421661693/50000000000000000000)
  centralHi := (578460811590843323387/100000000000000000000)
  directionLo := (580615235478554476831/100000000000000000000)
  directionHi := (18144226108704827401/3125000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree136.table
  base := (923471567078775099287133182801406649169/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (3090838757679889945948592516976984000000000000)
      linear := (-434212079692842961214492169352808645100000000000)
      constant := (15623067183900459225177146820255199529795699983048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree136.table
  base := (3693886268295335671948485282020913867359/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42849000000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (2622070771903007777692273791384000000000000)
      linear := (-368776011276583080752394965802905100000000000)
      constant := (13283002461915995754828160296695177876604931582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580615235478554476831/100000000000000000000)
  centralHi := (18144226108704827401/3125000000000000000)
  directionLo := (291380847342999447687/50000000000000000000)
  directionHi := (4662093557487991163/800000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree137.table
  base := (2365985962145105931085490438633512341461/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-2187019076980193919842910206889338065500000000000)
      constant := (79286734691586285458058166966980639615580319439824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree137.table
  base := (18927887697076725888464870509344531179719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1857433755542027569569369674216365500000000000)
      constant := (67410920855665788019591687115877351133039558862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291380847342999447687/50000000000000000000)
  centralHi := (4662093557487991163/800000000000000000)
  directionLo := (58490027689921426559/10000000000000000000)
  directionHi := (584900276899214265591/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree138.table
  base := (77565915424653728725417935505618697747969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1909620)
      previous := (954810)
      next := (954810)
      square := (6491994870153097975107314675440000000000000)
      linear := (-925426488341177497842201036343051000000000000)
      constant := (33802517114741527851998193445911411764408203121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree138.table
  base := (3878295771218365852868495934695779635521/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (81)
      square := (550739502605126607370777944000000000000)
      linear := (-78596406414666655550378681765100000000000)
      constant := (2873945619094332224483962590132324033439378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58490027689921426559/10000000000000000000)
  centralHi := (584900276899214265591/100000000000000000000)
  directionLo := (58703106820700524909/10000000000000000000)
  directionHi := (587031068207005249091/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree139.table
  base := (15888163854878396809364265616291549349183/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (6181677515359779891897185033953968000000000000)
      linear := (-887574573604860858953523570855971098200000000000)
      constant := (32662323127868619963173060010225077440283541930167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree139.table
  base := (79440819274148207849028322997953843187471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-3769082307720503802368318729240091000000000000)
      constant := (138850152260411282873116702614552633226739944879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58703106820700524909/10000000000000000000)
  centralHi := (587031068207005249091/100000000000000000000)
  directionLo := (589154153141380967083/100000000000000000000)
  directionHi := (147288538285345241771/25000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree140.table
  base := (81336262337922322371621480844400529462861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-4469790225056262522308516574530445171000000000000)
      constant := (165706964351351869073872478529785804168477375073589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree140.table
  base := (81336262337714845632052819351351929764811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-3796189706038728133983108419643771000000000000)
      constant := (140886645717324749777002298739308018838492386539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589154153141380967083/100000000000000000000)
  centralHi := (147288538285345241771/25000000000000000000)
  directionLo := (73908701839585707619/12500000000000000000)
  directionHi := (591269614716685660953/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree141.table
  base := (83252244615312953887175695012066100506139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-500189731343135638872157254975670539000000000000)
      constant := (18679981124368240792929393164732716650182633556379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree141.table
  base := (1040653057689204755613897042620760851251/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4761000000000000000000000000000000000000000
      center := (85698)
      previous := (42849)
      next := (42849)
      square := (291341196878111975299141532376000000000000)
      linear := (-42481078937299471839976645667193900000000000)
      constant := (1588200347731383565883517151799453439302448088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73908701839585707619/12500000000000000000)
  centralHi := (591269614716685660953/100000000000000000000)
  directionLo := (296688767233736889509/50000000000000000000)
  directionHi := (593377534467473779019/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree142.table
  base := (85188766106635160195738108484096184722837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-4533624939120178977390314015031624531000000000000)
      constant := (170550212943233594397795173572832245070352714586813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree142.table
  base := (85188766106484894623958334765516297130673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-3850404502675176797212687800451131000000000000)
      constant := (145004308995913684986149937374845849815752207377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296688767233736889509/50000000000000000000)
  centralHi := (593377534467473779019/100000000000000000000)
  directionLo := (297738996242589190551/50000000000000000000)
  directionHi := (595477992485178381103/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree143.table
  base := (87145826811962483615222991708651915352919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-4565542296152137204931212735282214211000000000000)
      constant := (172998112823113865440120416430072791727770579231631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree143.table
  base := (87145826811834612613861316812543886563353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-3877511900993401128827477490854811000000000000)
      constant := (147085478817595422390671989977626605995353112697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297738996242589190551/50000000000000000000)
  centralHi := (595477992485178381103/100000000000000000000)
  directionLo := (149392766863404879591/25000000000000000000)
  directionHi := (119514213490723903673/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree144.table
  base := (89123426731370052517323153807490733806941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-510828850353788381385790161725867099000000000000)
      constant := (19495947750995419439555415337813136900132695809501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree144.table
  base := (44561713365630621935515733351588366662051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (47610)
      previous := (23805)
      next := (23805)
      square := (161856220487839986277300851320000000000000)
      linear := (-24102588267355712718779427044805500000000000)
      constant := (920873708400450476650620248169862245964224979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149392766863404879591/25000000000000000000)
  centralHi := (119514213490723903673/20000000000000000000)
  directionLo := (14991420917084928217/2500000000000000000)
  directionHi := (599656836683397128681/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree145.table
  base := (91121565864934021236135788512750711221841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-4629377010216053660013010175783393571000000000000)
      constant := (177946463750772169458884349571425113755673305675609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree145.table
  base := (18224313172968287538247692705264158396769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (5244141543806015555384547582768000000000000)
      linear := (-786345339525969958411411374332434200000000000)
      constant := (30258498965149926762401968606359922923143154881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14991420917084928217/2500000000000000000)
  centralHi := (599656836683397128681/100000000000000000000)
  directionLo := (300867688072605490361/50000000000000000000)
  directionHi := (601735376145210980723/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree146.table
  base := (93140244212731106423035990273288818194437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-4661294367248011887553908896033983251000000000000)
      constant := (180446914798557923864567332136328160955862187735213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree146.table
  base := (46570122106326166152596830198057607567819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-1979417047974037061835923281032925500000000000)
      constant := (76709170506114348735273914616030073426673476331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300867688072605490361/50000000000000000000)
  centralHi := (601735376145210980723/100000000000000000000)
  directionLo := (301903380251074148221/50000000000000000000)
  directionHi := (603806760502148296443/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree147.table
  base := (95179461774838204547490775824501230944709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-521467969364441123899423068476063659000000000000)
      constant := (20329431433591102463483390008222890373259889006149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree147.table
  base := (11897432721846397904567644216375832271119/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (428490)
      previous := (214245)
      next := (214245)
      square := (1456705984390559876495707661880000000000000)
      linear := (-221441194125905469738146458470529500000000000)
      constant := (8642171073350748806385948038429627849771190236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301903380251074148221/50000000000000000000)
  centralHi := (603806760502148296443/100000000000000000000)
  directionLo := (605871063140977875809/100000000000000000000)
  directionHi := (60587106314097787581/10000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree148.table
  base := (48619609275666038814604214111794387810749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-2362564540655964171317853168267581305500000000000)
      constant := (92750184031031020793276737951206960088613248267301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree148.table
  base := (48619609275637529144226680771958429349849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-2006524446292261393450712971436605500000000000)
      constant := (78857354875003639611752842175127380739211679801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605871063140977875809/100000000000000000000)
  centralHi := (60587106314097787581/10000000000000000000)
  directionLo := (303964178101243916899/50000000000000000000)
  directionHi := (607928356202487833799/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree149.table
  base := (6207469658893068518899973362410937842661/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-2378523219171943285088302528392876145500000000000)
      constant := (94026685138894069774414994453662622171798446430312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree149.table
  base := (19863902908448117699122591332597686876507/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (5244141543806015555384547582768000000000000)
      linear := (-808031258180549423703243126655378200000000000)
      constant := (31977046460262676631885761211127522084971448443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303964178101243916899/50000000000000000000)
  centralHi := (607928356202487833799/100000000000000000000)
  directionLo := (38123669413181402029/6250000000000000000)
  directionHi := (121995742122180486493/20000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree150.table
  base := (101420349747785031015392767028090936893159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-532107088375093866413055975226260219000000000000)
      constant := (21180432172166893686863956371824680085485248106599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree150.table
  base := (101420349747743766046172891758008553643187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (856980)
      previous := (428490)
      next := (428490)
      square := (2913411968781119752991415323760000000000000)
      linear := (-451918187691219050014556147075619000000000000)
      constant := (18007849663803894056887399519647728723895213307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38123669413181402029/6250000000000000000)
  centralHi := (121995742122180486493/20000000000000000000)
  directionLo := (306011098051205972779/50000000000000000000)
  directionHi := (612022196102411945559/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree151.table
  base := (103541724167894883606909058993169270013849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-4820881152407803025258402497286931651000000000000)
      constant := (193211925877207540786938118374508365490631735359201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree151.table
  base := (103541724167859781586765017629869917903037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-4094371087539195781745795014084251000000000000)
      constant := (164270953768775491125196581388798057112227232413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306011098051205972779/50000000000000000000)
  centralHi := (612022196102411945559/100000000000000000000)
  directionLo := (76757360156606003113/12500000000000000000)
  directionHi := (122811776250569604981/20000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree152.table
  base := (105683637802692752714950991160307861313151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (30908387576798899459485925169769840000000000000)
      linear := (-4852798509439761252799301217537521331000000000000)
      constant := (195817479260908375045694680821656437197295673463799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree152.table
  base := (52841818901331447256514589753997863062647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-2060739242928710056680292352243965500000000000)
      constant := (83243076342468949469951267459889330434371361303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76757360156606003113/12500000000000000000)
  centralHi := (122811776250569604981/20000000000000000000)
  directionLo := (616088833504535642323/100000000000000000000)
  directionHi := (154022208376133910581/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree153.table
  base := (107846090652251727500143424314878414713837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-542746207385746608926688881976456779000000000000)
      constant := (22048949966734248627919592100204129768298822171757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree153.table
  base := (53923045326113165426233898530930910996263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2645000000000000000000000000000000000000000
      center := (47610)
      previous := (23805)
      next := (23805)
      square := (161856220487839986277300851320000000000000)
      linear := (-25608554840590397808489965400565500000000000)
      constant := (1041458294584724738383684613890053951917023127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616088833504535642323/100000000000000000000)
  centralHi := (154022208376133910581/25000000000000000000)
  directionLo := (123622423838470270841/20000000000000000000)
  directionHi := (309056059596175677103/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree154.table
  base := (550145413583219025158751183149717082291/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (3090838757679889945948592516976984000000000000)
      linear := (-491663322350367770788109865803870069100000000000)
      constant := (20108113719631076513598119593717507046548121353180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree154.table
  base := (11002908271662220419442883300143439772969/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42849000000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (2622070771903007777692273791384000000000000)
      linear := (-417569328249386877659016408529529100000000000)
      constant := (17096122688214110715514966983418763650831948681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123622423838470270841/20000000000000000000)
  centralHi := (309056059596175677103/50000000000000000000)
  directionLo := (310064401784508187037/50000000000000000000)
  directionHi := (24805152142760654963/4000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree155.table
  base := (56116306997969913708109708922812184453783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-2474275290267817967710998689144645185500000000000)
      constant := (101869620874009767847785984618300667563496945295567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree155.table
  base := (22446522799184291167591602540735477232129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (1542564)
      previous := (771282)
      next := (771282)
      square := (5244141543806015555384547582768000000000000)
      linear := (-840560136162418621640990755139794200000000000)
      constant := (34644220432637607462920726471690575463919495521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310064401784508187037/50000000000000000000)
  centralHi := (24805152142760654963/4000000000000000000)
  directionLo := (622138950829651738097/100000000000000000000)
  directionHi := (311069475414825869049/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree156.table
  base := (114456684490209435365883031670392206317837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-553385326396399351440321788726653339000000000000)
      constant := (22934984817304229649339612093673747269000918415757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree156.table
  base := (2861417112254845273316202552171251890699/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4761000000000000000000000000000000000000000
      center := (85698)
      previous := (42849)
      next := (42849)
      square := (291341196878111975299141532376000000000000)
      linear := (-46998978657003527109108260734473900000000000)
      constant := (1949954106287435397216152171664621721006471756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622138950829651738097/100000000000000000000)
  centralHi := (311069475414825869049/50000000000000000000)
  directionLo := (624142624135621706051/100000000000000000000)
  directionHi := (156035656033905426513/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree157.table
  base := (58350647099760517713510909149621254516177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-2506192647299776195251897409395234865500000000000)
      constant := (104554001009734906879197723971561810334050861856473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree157.table
  base := (116701294199507747897775750607103544257963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-4257015477448541771434533156506331000000000000)
      constant := (177785529090187486691487444260823486767909456587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624142624135621706051/100000000000000000000)
  centralHi := (156035656033905426513/25000000000000000000)
  directionLo := (626139885637690452729/100000000000000000000)
  directionHi := (62613988563769045273/10000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree158.table
  base := (59483221561970889263411501911273691617277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-2522151325815755309022346769520529705500000000000)
      constant := (105909328869609084097460426223222070078284580150373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree158.table
  base := (118966443123930478835593036374139983797133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-4284122875766766103049322846910011000000000000)
      constant := (180090080736145820112074278086398102165723351917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626139885637690452729/100000000000000000000)
  centralHi := (62613988563769045273/10000000000000000000)
  directionLo := (125626159299703213807/20000000000000000000)
  directionHi := (157032699124629017259/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree159.table
  base := (30313032815884386967606692352279087525311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-282012222703526046976977347738424949500000000000)
      constant := (11919268361943692104334594826201223821500273814142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree159.table
  base := (60626065631763969508999034568122494049569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (428490)
      previous := (214245)
      next := (214245)
      square := (1456705984390559876495707661880000000000000)
      linear := (-239512793004721690814672918739649500000000000)
      constant := (10133862472430389515093319946174671694169998009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125626159299703213807/20000000000000000000)
  centralHi := (157032699124629017259/25000000000000000000)
  directionLo := (630115416914504905421/100000000000000000000)
  directionHi := (315057708457252452711/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree160.table
  base := (24711671723674590906585850297202761198123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101018898000000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (6181677515359779891897185033953968000000000000)
      linear := (-1021627473139085414625298195908447754200000000000)
      constant := (43458504069355589255500682938323427581395772564227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree160.table
  base := (1930599353411949747381159907955142564257/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-2169168836201607383139451113858685500000000000)
      constant := (92371930196496915294499367374084716919547142176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630115416914504905421/100000000000000000000)
  centralHi := (315057708457252452711/50000000000000000000)
  directionLo := (316046903068524175087/50000000000000000000)
  directionHi := (25283752245481934007/4000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree161.table
  base := (125885125188511339355893212454047247292023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (17186580)
      previous := (8593290)
      next := (8593290)
      square := (58427953831377881775965832078960000000000000)
      linear := (-9716549570373129112792797164069619000000000000)
      constant := (415984361502071517399564286076015446718689648063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree161.table
  base := (125885125188504391831186883098686675596033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (14580)
      previous := (7290)
      next := (7290)
      square := (49566555234461394663370014960000000000000)
      linear := (-8252259112894969939307546159019000000000000)
      constant := (353673134978996207507794370807192620723278673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316046903068524175087/50000000000000000000)
  centralHi := (25283752245481934007/4000000000000000000)
  directionLo := (634066022493163238923/100000000000000000000)
  directionHi := (158516505623290809731/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree162.table
  base := (16029053871751847497652593899859816285093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (1717132643155494414415884731653880000000000000)
      linear := (-287331782208852418233793801113523229500000000000)
      constant := (12379802843246847370339371062559190187189455263892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree162.table
  base := (25646486194801774549503100635357979017111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (19044)
      previous := (9522)
      next := (9522)
      square := (64742488195135994510920340528000000000000)
      linear := (-10845808565530033159280201502530200000000000)
      constant := (467795576633173239900021025035044770900051719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (634066022493163238923/100000000000000000000)
  centralHi := (158516505623290809731/25000000000000000000)
  directionLo := (159008030851389059317/25000000000000000000)
  directionHi := (636032123405556237269/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree163.table
  base := (65300137987472051021797457199514272555777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-2601944718395650877874593570147003905500000000000)
      constant := (112817346089161639216006923022275132184678118036873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree163.table
  base := (65300137987469539761888606271484563444649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 214245000000000000000000000000000000000000000
      center := (3856410)
      previous := (1928205)
      next := (1928205)
      square := (13110353859515038888461368956920000000000000)
      linear := (-2209829933678943880561635649464205500000000000)
      constant := (95918110395317471620191693906232908559039765001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159008030851389059317/25000000000000000000)
  centralHi := (636032123405556237269/100000000000000000000)
  directionLo := (15949804135303293087/2500000000000000000)
  directionHi := (637992165412131723481/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree164.table
  base := (66494330095679446850765558303813665188593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-2617903396911629991645042930272298745500000000000)
      constant := (114225225117119459883569273168375936894346313515257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree164.table
  base := (132988660191354623554584571688006000864399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-4446767265676112092738060989332091000000000000)
      constant := (194230125166490891302895593781292453131038632751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15949804135303293087/2500000000000000000)
  centralHi := (637992165412131723481/100000000000000000000)
  directionLo := (159986551046240480177/25000000000000000000)
  directionHi := (639946204184961920709/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree165.table
  base := (135397583623317522820984683610464688226501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-585302683428357578981220508977243019000000000000)
      constant := (25698191705132569422247943262969554062641928078661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree165.table
  base := (135397583623313892476511734019106788786629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (856980)
      previous := (428490)
      next := (428490)
      square := (2913411968781119752991415323760000000000000)
      linear := (-497097184888259602705872297748419000000000000)
      constant := (21848769073778389799876077660557602421413140669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159986551046240480177/25000000000000000000)
  centralHi := (639946204184961920709/100000000000000000000)
  directionLo := (320947147274368643051/50000000000000000000)
  directionHi := (641894294548737286103/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree166.table
  base := (13782704627087715623831546284914657277337/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (3090838757679889945948592516976984000000000000)
      linear := (-529964150788717643837188330104577685100000000000)
      constant := (23413451751418878099669828419447217911202132057313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree166.table
  base := (110261637016699255957691590969710644819/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42849000000000000000000000000000000000000000
      center := (771282)
      previous := (385641)
      next := (385641)
      square := (2622070771903007777692273791384000000000000)
      linear := (-450098206231256075596764037013945100000000000)
      constant := (19906261028318124419089331131404044027481166375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320947147274368643051/50000000000000000000)
  centralHi := (641894294548737286103/100000000000000000000)
  directionLo := (643836490498714455941/100000000000000000000)
  directionHi := (321918245249357227971/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree167.table
  base := (1753463101676172257806132070206286093843/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (3090838757679889945948592516976984000000000000)
      linear := (-533155886491913466591278202129636653100000000000)
      constant := (23700282673822871621244082390851296750940977780056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree167.table
  base := (140277048134091156948468688945807981322791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-4528089460630785087582430060543131000000000000)
      constant := (201501191024020498865002399121212943191700271559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643836490498714455941/100000000000000000000)
  centralHi := (321918245249357227971/50000000000000000000)
  directionLo := (10090200706534037023/1562500000000000000)
  directionHi := (645772845218178369473/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree168.table
  base := (142747589213022224552479846110104476740597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (1010188980)
      previous := (505094490)
      next := (505094490)
      square := (3434265286310988828831769463307760000000000000)
      linear := (-595941802439010321494853415727439579000000000000)
      constant := (26654294779812855534274363570886443582288985600117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree168.table
  base := (4460862162906874819642708289885524127531/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 23805000000000000000000000000000000000000000
      center := (428490)
      previous := (214245)
      next := (214245)
      square := (1456705984390559876495707661880000000000000)
      linear := (-253066492163833856622067763941489500000000000)
      constant := (11330814660362534560690149207696635685938801456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell096.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10090200706534037023/1562500000000000000)
  centralHi := (645772845218178369473/100000000000000000000)
  directionLo := (647703411095434548107/100000000000000000000)
  directionHi := (161925852773858637027/25000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 7339
  qDenominator := 14214
  table := BinomialMassData.Q7339_14214.Degree169.table
  base := (72619334753858090718602017343899454855213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (15454193788399449729742962584884920000000000000)
      linear := (-2697696789491525560497289730898772945500000000000)
      constant := (121395998177226221904793101675959853426887183407637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7339_14214.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree169.table
  base := (145238669507714285559630363471817945533359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (7712820)
      previous := (3856410)
      next := (3856410)
      square := (26220707719030077776922737913840000000000000)
      linear := (-4582304257267233750812009441350491000000000000)
      constant := (206423028870698915026090109320236966148158899791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell096.Kernel169
