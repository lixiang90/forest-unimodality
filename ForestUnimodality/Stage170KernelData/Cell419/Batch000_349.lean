import ForestUnimodality.FiniteKernelDegreeCertificate
import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell419.Parameters
import ForestUnimodality.BinomialMassData.Q467_742.Batch000_049
import ForestUnimodality.BinomialMassData.Q467_742.Batch050_099
import ForestUnimodality.BinomialMassData.Q236_371.Batch000_049
import ForestUnimodality.BinomialMassData.Q236_371.Batch050_099

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree000.table
  base := (570519431136915552482236091/50000000000000000000000000)
  polynomial :=
    { denominator := 7420000000000000000000000000000000000000000
      center := (14477)
      previous := (0)
      next := (8525)
      square := (164765475982129588616853507460000000000000)
      linear := (-420225143299591194639974747540000000000000)
      constant := (84665083580718267988363835904400000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree000.table
  base := (570519431136915552482236091/50000000000000000000000000)
  polynomial :=
    { denominator := 3710000000000000000000000000000000000000000
      center := (7316)
      previous := (0)
      next := (4185)
      square := (82382737991064794308426753730000000000000)
      linear := (-210112571649795597319987373770000000000000)
      constant := (42332541790359133994181917952200000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree001.table
  base := (11516784509030931848984002621233057124149/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-33264143635400407299357317045880000000000000)
      constant := (3640749190143039102473551200459264635714268592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree001.table
  base := (22975390551816924425939480149811127725387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-16690916630550964217041820489890000000000000)
      constant := (1815911016564261708798722817145544817857138324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (48111508724453423913/100000000000000000000)
  directionHi := (24055754362226711957/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree002.table
  base := (74265256938916020199197755453611414113527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-44256354675922481282795972472140000000000000)
      constant := (2962427071408738607681952459433482471428562802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree002.table
  base := (2309005591678340845719556589916749835169/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-22245866963662761776124310169970000000000000)
      constant := (1474098067358977714417052096831537664285697504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48111508724453423913/100000000000000000000)
  centralHi := (24055754362226711957/50000000000000000000)
  directionLo := (68039948144353518831/100000000000000000000)
  directionHi := (4252496759022094927/6250000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree003.table
  base := (2389497031161520482590142273198747602527/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-55248565716444555266234627898400000000000000)
      constant := (2422418789295723368458226649894503705424420050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree003.table
  base := (11855835333526101185915296797413668387977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-27800817296774559335206799850050000000000000)
      constant := (1202759069123844134054396664081364807563958755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68039948144353518831/100000000000000000000)
  centralHi := (4252496759022094927/6250000000000000000)
  directionLo := (41665788769773319197/50000000000000000000)
  directionHi := (16666315507909327679/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree004.table
  base := (47922056574580281089764468505392701203481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-66240776756966629249673283324660000000000000)
      constant := (1995999064418821755478749828844633367528093806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree004.table
  base := (47427039972279697962905178704061930075533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-33355767629886356894289289530130000000000000)
      constant := (989161925825872755267411398940049731075205379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41665788769773319197/50000000000000000000)
  centralHi := (16666315507909327679/20000000000000000000)
  directionLo := (96223017448906847827/100000000000000000000)
  directionHi := (24055754362226711957/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree005.table
  base := (38299232552313648297755942279597481499369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-77232987797488703233111938750920000000000000)
      constant := (1662721649754023076314683913759425557444185294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree005.table
  base := (37797919052208018153967288490869592830163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-38910717962998154453371779210210000000000000)
      constant := (822809548937199736583252203061768803819495069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96223017448906847827/100000000000000000000)
  centralHi := (24055754362226711957/25000000000000000000)
  directionLo := (5379030200397602719/5000000000000000000)
  directionHi := (107580604007952054381/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree006.table
  base := (15228271801643427146005276587032940637043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-88225198838010777216550594177180000000000000)
      constant := (1406368105356710103930719449933714846984706036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree006.table
  base := (29969160472240634652504118883821709834871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-44465668296109952012454268890290000000000000)
      constant := (695391303961982359330282367207386280483068473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5379030200397602719/5000000000000000000)
  centralHi := (107580604007952054381/100000000000000000000)
  directionLo := (117848647130372046337/100000000000000000000)
  directionHi := (58924323565186023169/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree007.table
  base := (24058843631665185581647176245580327293273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-99217409878532851199989249603440000000000000)
      constant := (1213758475862086895584465317850526951135253998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree007.table
  base := (23598165755399093458275401506865523724601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-50020618629221749571536758570370000000000000)
      constant := (600170677047393282501777494298576792996829463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117848647130372046337/100000000000000000000)
  centralHi := (58924323565186023169/50000000000000000000)
  directionLo := (31822771821254533709/25000000000000000000)
  directionHi := (127291087285018134837/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree008.table
  base := (18834112064047273130014201513575880221421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-110209620919054925183427905029700000000000000)
      constant := (1074195280200571212540560303414165065587602246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree008.table
  base := (9203781201502296910565279960820302814191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-55575568962333547130619248250450000000000000)
      constant := (531693692751911246947526799827859228470875266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31822771821254533709/25000000000000000000)
  centralHi := (127291087285018134837/100000000000000000000)
  directionLo := (68039948144353518831/50000000000000000000)
  directionHi := (136079896288707037663/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree009.table
  base := (14561636226732311189545088296037593549573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-121201831959576999166866560455960000000000000)
      constant := (978998771766205167970202627763709403930507798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree009.table
  base := (3543214340535767603038099300919254416681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-61130519295445344689701737930530000000000000)
      constant := (485546144176086986105031440669381198380794012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68039948144353518831/50000000000000000000)
  centralHi := (136079896288707037663/100000000000000000000)
  directionLo := (7216726308668013587/5000000000000000000)
  directionHi := (144334526173360271741/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree010.table
  base := (1382794358468113952023315977996798568173/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-132194043000099073150305215882220000000000000)
      constant := (921127187763804647720351870249816803935771184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree010.table
  base := (669523547109178879934214521345808041101/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-66685469628557142248784227610610000000000000)
      constant := (458155777835813078734778399695161976194703408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7216726308668013587/5000000000000000000)
  centralHi := (144334526173360271741/100000000000000000000)
  directionLo := (152141949236335141853/100000000000000000000)
  directionHi := (76070974618167570927/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree011.table
  base := (2047751372374931332160161152490497588683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-143186254040621147133743871308480000000000000)
      constant := (894867935213328213819887779454040232690190632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree011.table
  base := (3939553042448208851738332443208598713983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-72240419961668939807866717290690000000000000)
      constant := (446631847756812391202766811080621353026095458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152141949236335141853/100000000000000000000)
  centralHi := (76070974618167570927/50000000000000000000)
  directionLo := (159567822536922327893/100000000000000000000)
  directionHi := (79783911268461163947/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree012.table
  base := (2914873869834442304920516338159019204207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-154178465081143221117182526734740000000000000)
      constant := (895586824419130140427456873898043178449288964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree012.table
  base := (555408104049730903651259172034702734367/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-77795370294780737366949206970770000000000000)
      constant := (448635158611383180844436281016863598658583210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159567822536922327893/100000000000000000000)
  centralHi := (79783911268461163947/50000000000000000000)
  directionLo := (41665788769773319197/25000000000000000000)
  directionHi := (166663155079093276789/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree013.table
  base := (1941494085737779826004610753684001324837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-165170676121665295100621182161000000000000000)
      constant := (919524547493264818522363022082409072201079724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree013.table
  base := (72820738798329848336588407617269410757/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-83350320627892534926031696650850000000000000)
      constant := (462272857984237910149104052314558421185744550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41665788769773319197/25000000000000000000)
  centralHi := (166663155079093276789/100000000000000000000)
  directionLo := (173468511645949891193/100000000000000000000)
  directionHi := (86734255822974945597/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree014.table
  base := (2273180998109391911734479228355924756363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-176162887162187369084059837587260000000000000)
      constant := (963631538823628088026435782300485096968731338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree014.table
  base := (1031039056081075432857394210775090495599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-88905270961004332485114186330930000000000000)
      constant := (486013283296664481864348942189821208829926274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173468511645949891193/100000000000000000000)
  centralHi := (86734255822974945597/50000000000000000000)
  directionLo := (45004195501922520031/25000000000000000000)
  directionHi := (1440134256061520641/800000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree015.table
  base := (468710578719286950007227571066833256221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-187155098202709443067498493013520000000000000)
      constant := (1025433993936824487627168711036223569268294092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree015.table
  base := (47135821656880684407587475060575949953/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-94460221294116130044196676011010000000000000)
      constant := (518617047919593080524027164647257678462813424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45004195501922520031/25000000000000000000)
  centralHi := (1440134256061520641/800000000000000000)
  directionLo := (186335072050720953051/100000000000000000000)
  directionHi := (46583768012680238263/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree016.table
  base := (-35063928656271152651578853402558807429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-198147309243231517050937148439780000000000000)
      constant := (1102925174192385329090472214990654861695235730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree016.table
  base := (-333681320805430127212730877671874266979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-100015171627227927603279165691090000000000000)
      constant := (559081272711297905481980712627537936288391923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186335072050720953051/100000000000000000000)
  centralHi := (46583768012680238263/25000000000000000000)
  directionLo := (96223017448906847827/50000000000000000000)
  directionHi := (38489206979562739131/20000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree017.table
  base := (-1106435175149140577099170014907121145673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-209139520283753591034375803866040000000000000)
      constant := (1194477228148081425574019442615497553825263602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree017.table
  base := (-1242755734154950846277811945913098874727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-105570121960339725162361655371170000000000000)
      constant := (606594456924121058629757707909790736826242999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96223017448906847827/50000000000000000000)
  centralHi := (38489206979562739131/20000000000000000000)
  directionLo := (4959220806968676703/2500000000000000000)
  directionHi := (198368832278747068121/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree018.table
  base := (-75580146599066522697537572440638925349/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-220131731324275665017814459292300000000000000)
      constant := (1298769658456308684863123896831265840543130650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree018.table
  base := (-2006444850790206756345682766184445567783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-111125072293451522721444145051250000000000000)
      constant := (660499959446221663854160777043155246800682871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4959220806968676703/2500000000000000000)
  centralHi := (198368832278747068121/100000000000000000000)
  directionLo := (102059922216530278247/50000000000000000000)
  directionHi := (40823968886612111299/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree019.table
  base := (-2551763383667160313178338318327101733883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-231123942364797739001253114718560000000000000)
      constant := (1414731292875526405592860507892303397213317142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree019.table
  base := (-265177060618614835956516433195638111661/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-116680022626563320280526634731330000000000000)
      constant := (720266447960355769431437652833021678104097570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102059922216530278247/50000000000000000000)
  centralHi := (40823968886612111299/20000000000000000000)
  directionLo := (8388528182046717123/4000000000000000000)
  directionHi := (52428301137791982019/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree020.table
  base := (-623061932026428946017616585179850955611/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-242116153405319812984691770144820000000000000)
      constant := (1541493210500960450500689091745485906598209070) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree020.table
  base := (-1600299108162949589955487208109646564197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-122234972959675117839609124411410000000000000)
      constant := (785463986724647217509673459709080039216388778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8388528182046717123/4000000000000000000)
  centralHi := (52428301137791982019/25000000000000000000)
  directionLo := (5379030200397602719/2500000000000000000)
  directionHi := (215161208015904108761/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree021.table
  base := (-224879119128695946931296513167108039329/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-253108364445841886968130425571080000000000000)
      constant := (1678350555244587453970548895219019947925563936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree021.table
  base := (-1835310114091240885757787674467086217089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-127789923292786915398691614091490000000000000)
      constant := (855744687187965465606961590877307367426757986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5379030200397602719/2500000000000000000)
  centralHi := (215161208015904108761/100000000000000000000)
  directionLo := (220474630528336108677/100000000000000000000)
  directionHi := (110237315264168054339/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree022.table
  base := (-4014571312993725134759748564189841604571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-264100575486363960951569080997340000000000000)
      constant := (1824731558859685403695565532039230289058640854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree022.table
  base := (-4076152793744667521126834905029900771203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-133344873625898712957774103771570000000000000)
      constant := (930827050853755301945678722279277061135835411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220474630528336108677/100000000000000000000)
  centralHi := (110237315264168054339/50000000000000000000)
  directionLo := (14103936171878672899/6250000000000000000)
  directionHi := (45132595750011753277/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree023.table
  base := (-2188309915558397782773098282974023101901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-275092786526886034935007736423600000000000000)
      constant := (1980172412461440978036230840816682134989282548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree023.table
  base := (-442877999659341380356504342737930953883/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-138899823959010510516856593451650000000000000)
      constant := (1010483299886564361664733484903080636537985710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14103936171878672899/6250000000000000000)
  centralHi := (45132595750011753277/20000000000000000000)
  directionLo := (14420918135929291269/6250000000000000000)
  directionHi := (46146938034973732061/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree024.table
  base := (-1173444626557441111572280078386245676721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-286084997567408108918446391849860000000000000)
      constant := (2144296882406667612605425105281290010069079816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree024.table
  base := (-4737875224437061591608162075508561595867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-144454774292122308075939083131730000000000000)
      constant := (1094529125363883536216392828468955153340467179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14420918135929291269/6250000000000000000)
  centralHi := (46146938034973732061/20000000000000000000)
  directionLo := (117848647130372046337/50000000000000000000)
  directionHi := (9427891770429763707/4000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree025.table
  base := (-1243451987855319035513311627449597473891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-297077208607930182901885047276120000000000000)
      constant := (2316799774825041279102612883118043518967050136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree025.table
  base := (-2505511524614492927514846684342178011249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-150009724625234105635021572811810000000000000)
      constant := (1182815391847393613570000372940559507529621826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117848647130372046337/50000000000000000000)
  centralHi := (9427891770429763707/4000000000000000000)
  directionLo := (15034846476391694973/6250000000000000000)
  directionHi := (240557543622267119569/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree026.table
  base := (-1044600686032150398144143932478518922597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-308069419648452256885323702702380000000000000)
      constant := (2497433522185363513994240959417748824249751890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree026.table
  base := (-5254360599962345422018748834207863678877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-155564674958345903194104062491890000000000000)
      constant := (1275221424969702111686873618356570776482241549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15034846476391694973/6250000000000000000)
  centralHi := (240557543622267119569/100000000000000000000)
  directionLo := (61330380453594380329/25000000000000000000)
  directionHi := (245321521814377521317/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree027.table
  base := (-85101117803516505733693985832791537919/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-319061630688974330868762358128640000000000000)
      constant := (2685997302454922148882238447268571958707033984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree027.table
  base := (-2736426895365583705309282737912390657829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-161119625291457700753186552171970000000000000)
      constant := (1371649579961978175344928395512337324990216746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61330380453594380329/25000000000000000000)
  centralHi := (245321521814377521317/100000000000000000000)
  directionLo := (124997366309319957591/50000000000000000000)
  directionHi := (249994732618639915183/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree028.table
  base := (-5648354651765341353040539607514233530549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-330053841729496404852201013554900000000000000)
      constant := (2882328212690770576978853933857175252177630026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree028.table
  base := (-226820833411063912327418037234746395073/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-166674575624569498312269041852050000000000000)
      constant := (1472020846687429650994777627334969540841990025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124997366309319957591/50000000000000000000)
  centralHi := (249994732618639915183/100000000000000000000)
  directionLo := (31822771821254533709/12500000000000000000)
  directionHi := (254582174570036269673/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree029.table
  base := (-1166402595939128442738522742472681186987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-341046052770018478835639668981160000000000000)
      constant := (3086294109175581847463727555712531698202746190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree029.table
  base := (-585061310716436457171885273181915835119/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-172229525957681295871351531532130000000000000)
      constant := (1576271293387633629817941176993319889340551030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31822771821254533709/12500000000000000000)
  centralHi := (254582174570036269673/100000000000000000000)
  directionLo := (259088403601071230643/100000000000000000000)
  directionHi := (64772100900267807661/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree030.table
  base := (-6000172263609760780966862875689442796469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-352038263810540552819078324407420000000000000)
      constant := (3297787799442629309489494842086236972586060106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree030.table
  base := (-93996273207285379102720026945058248789/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-177784476290793093430434021212210000000000000)
      constant := (1684349189091333976028489567326276457859961152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259088403601071230643/100000000000000000000)
  centralHi := (64772100900267807661/25000000000000000000)
  directionLo := (131758793019948708241/50000000000000000000)
  directionHi := (263517586039897416483/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree031.table
  base := (-1231008714761928793894732820207111308963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-363030474851062626802516979833680000000000000)
      constant := (3516722330941218598692188106936950703318605310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree031.table
  base := (-6168094770996321498139294592424766897567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-183339426623904890989516510892290000000000000)
      constant := (1796212675176326723574719473464951808493140079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131758793019948708241/50000000000000000000)
  centralHi := (263517586039897416483/100000000000000000000)
  directionLo := (133936771858998729271/50000000000000000000)
  directionHi := (267873543717997458543/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree032.table
  base := (-6298420491795051521676909112038541440601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-374022685891584700785955635259940000000000000)
      constant := (3743027169285290163439672344340932319306925074) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree032.table
  base := (-630933550690337819808225959893189785689/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-188894376957016688548599000572370000000000000)
      constant := (1911827881288473993790203568048282092439971930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133936771858998729271/50000000000000000000)
  centralHi := (267873543717997458543/100000000000000000000)
  directionLo := (10886391703096563013/4000000000000000000)
  directionHi := (136079896288707037663/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree033.table
  base := (-1607939485471002061772104740375796287691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-385014896932106774769394290686200000000000000)
      constant := (3976645098121113360073085679575580740761054936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree033.table
  base := (-1288175501839725689417818240544027612191/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-194449327290128486107681490252450000000000000)
      constant := (2031167400819615077387758782474553925307441835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10886391703096563013/4000000000000000000)
  centralHi := (136079896288707037663/50000000000000000000)
  directionLo := (276379575887083616343/100000000000000000000)
  directionHi := (34547446985885452043/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree034.table
  base := (-3278118068915668261289543702536427053439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-396007107972628848752832946112460000000000000)
      constant := (4217529704362566043799603344806464939392915772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree034.table
  base := (-6563848603839390772886554082528235392981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-200004277623240283666763979932530000000000000)
      constant := (2154209057327951220156693742865727307467814597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276379575887083616343/100000000000000000000)
  centralHi := (34547446985885452043/12500000000000000000)
  directionLo := (280535892960717897263/100000000000000000000)
  directionHi := (17533493310044868579/6250000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree035.table
  base := (-1668203113739406865027807672770335031587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-406999319013150922736271601538720000000000000)
      constant := (4465643338267790648550195291251610218191238552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree035.table
  base := (-3339580694934942575085210558082836898709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-205559227956352081225846469612610000000000000)
      constant := (2280934906378475924734565467125434356121369866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280535892960717897263/100000000000000000000)
  centralHi := (17533493310044868579/6250000000000000000)
  directionLo := (284631524099159697041/100000000000000000000)
  directionHi := (142315762049579848521/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree036.table
  base := (-3391131753825380982576237689320330338159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-417991530053672996719710256964980000000000000)
      constant := (4720955458699369369836441636847377378243118332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree036.table
  base := (-6787554314871594956603452244728961163277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-211114178289463878784928959292690000000000000)
      constant := (2411330427876394483466391106531894436646484349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284631524099159697041/100000000000000000000)
  centralHi := (142315762049579848521/50000000000000000000)
  directionLo := (288669052346720543481/100000000000000000000)
  directionHi := (144334526173360271741/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree037.table
  base := (-6885219281639861196175246701622085812147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-428983741094195070703148912391240000000000000)
      constant := (4983441290838518788980255786846544853351507078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree037.table
  base := (-861203113919094576523518129344374935097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-216669128622575676344011448972770000000000000)
      constant := (2545383872539997443625661551434292445209501512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288669052346720543481/100000000000000000000)
  centralHi := (144334526173360271741/50000000000000000000)
  directionLo := (292650882545221180881/100000000000000000000)
  directionHi := (146325441272610590441/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree038.table
  base := (-349109541062619371445520206825048488191/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-439975952134717144686587567817500000000000000)
      constant := (5253080737356017124526245961477242863068014680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree038.table
  base := (-69858566900878942754372834193953520771/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-222224078955687473903093938652850000000000000)
      constant := (2683085733096925336683539931355069192107982700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292650882545221180881/100000000000000000000)
  centralHi := (146325441272610590441/50000000000000000000)
  directionLo := (296579258084984765109/100000000000000000000)
  directionHi := (29657925808498476511/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree039.table
  base := (-7073592688604934950269403762079942624927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-450968163175239218670026223243760000000000000)
      constant := (5529857495182067189547332238984479176332120798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree039.table
  base := (-353832045046357249189257082656041947291/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-227779029288799271462176428332930000000000000)
      constant := (2824428316401374918072956111628564943808341340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296579258084984765109/100000000000000000000)
  centralHi := (29657925808498476511/10000000000000000000)
  directionLo := (300456275684138704741/100000000000000000000)
  directionHi := (150228137842069352371/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree040.table
  base := (-286390447275989095175200581528825735597/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-461960374215761292653464878670020000000000000)
      constant := (5813758339053568337997695977252734978047809450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree040.table
  base := (-7162294140583929612549135622757659245813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-233333979621911069021258918013010000000000000)
      constant := (2969405397212170193122543743672116146249578981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300456275684138704741/100000000000000000000)
  centralHi := (150228137842069352371/50000000000000000000)
  directionLo := (152141949236335141853/50000000000000000000)
  directionHi := (304283898472670283707/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree041.table
  base := (-1810242278401147616694704841413782480817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-472952585256283366636903534096280000000000000)
      constant := (6104772540347410854411735517127821360637562632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree041.table
  base := (-1448614519996461899762782495739650408269/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-238888929955022866580341407693090000000000000)
      constant := (3118011938047171343761207410567556270111033265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152141949236335141853/50000000000000000000)
  centralHi := (304283898472670283707/100000000000000000000)
  directionLo := (61612793522601935319/20000000000000000000)
  directionHi := (77015991903252419149/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree042.table
  base := (-7317437798093131815297448696303633659701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-483944796296805440620342189522540000000000000)
      constant := (6402891395654538246200494159457523302698598474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree042.table
  base := (-1463836718497967416382178404592388187469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-244443880288134664139423897373170000000000000)
      constant := (3270243862503632186374373404747779355348985265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61612793522601935319/20000000000000000000)
  centralHi := (77015991903252419149/25000000000000000000)
  directionLo := (155899106326185071611/50000000000000000000)
  directionHi := (311798212652370143223/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree043.table
  base := (-7389346775669400172584449849844782578491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-494937007337327514603780844948800000000000000)
      constant := (6708107844372953492313945132348159080318262934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree043.table
  base := (-1478158976394156418638374899813821956741/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-249998830621246461698506387053250000000000000)
      constant := (3426097871840689585234471278024444094323008585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155899106326185071611/50000000000000000000)
  centralHi := (311798212652370143223/100000000000000000000)
  directionLo := (157744130386011344917/50000000000000000000)
  directionHi := (63097652154404537967/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree044.table
  base := (-932105212550909386621668744298588222887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-505929218377849588587219500375060000000000000)
      constant := (7020416158510547205398368147959669756373966704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree044.table
  base := (-7458042230560135268629206063707513107989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-255553780954358259257588876733330000000000000)
      constant := (3585571296567483217500076787918599169757612293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157744130386011344917/50000000000000000000)
  centralHi := (63097652154404537967/20000000000000000000)
  directionLo := (319135645073844655787/100000000000000000000)
  directionHi := (79783911268461163947/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree045.table
  base := (-1880010184631691494002655479815441878213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-516921429418371662570658155801320000000000000)
      constant := (7339811691062551295807198612659886730789582248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree045.table
  base := (-7521035505923674208405725453808539083017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-261108731287470056816671366413410000000000000)
      constant := (3748661976356100898218794776345962696010636729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319135645073844655787/100000000000000000000)
  centralHi := (79783911268461163947/25000000000000000000)
  directionLo := (322741812023856163141/100000000000000000000)
  directionHi := (161370906011928081571/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree046.table
  base := (-7579039758560321086750208451972884943689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-527913640458893736554096811227580000000000000)
      constant := (7666290671903058703068925175533314326704486386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree046.table
  base := (-3789931811463524445902111886872578555091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-266663681620581854375753856093490000000000000)
      constant := (3915368162873539351847987721821248975742491334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322741812023856163141/100000000000000000000)
  centralHi := (161370906011928081571/50000000000000000000)
  directionLo := (326308128155253381461/100000000000000000000)
  directionHi := (163154064077626690731/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree047.table
  base := (-3816958270727440326721283673094796948551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-538905851499415810537535466653840000000000000)
      constant := (7999850042218550055767370333386183030402566748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree047.table
  base := (-763459854216895708528155661802896067581/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-272218631953693651934836345773570000000000000)
      constant := (4085688441158546384205814472789576546231547970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326308128155253381461/100000000000000000000)
  centralHi := (163154064077626690731/50000000000000000000)
  directionLo := (164917943059517043027/50000000000000000000)
  directionHi := (65967177223806817211/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree048.table
  base := (-1921183548918928826650554751604948488081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-549898062539937884520974122080100000000000000)
      constant := (8340487320205520121086920056790815183030906376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree048.table
  base := (-1921324626344644676599180419421671421587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-277773582286805449493918835453650000000000000)
      constant := (4259621666004001130573312457652286699349339276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (164917943059517043027/50000000000000000000)
  centralHi := (65967177223806817211/20000000000000000000)
  directionLo := (41665788769773319197/12500000000000000000)
  directionHi := (333326310158186553577/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree049.table
  base := (-483221495464544621491472249397855945847/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-560890273580459958504412777506360000000000000)
      constant := (8688200492128558808239204224023013673177934048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree049.table
  base := (-7732010653324699242973291345502731904937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-283328532619917247053001325133730000000000000)
      constant := (4437166910480966961903406772450059782553223769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel049

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41665788769773319197/12500000000000000000)
  centralHi := (333326310158186553577/100000000000000000000)
  directionLo := (67356112214234793479/20000000000000000000)
  directionHi := (84195140267793491849/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree050.table
  base := (-7774387287802845554430972930876068293507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-571882484620982032487851432932620000000000000)
      constant := (9042987923950013234754770811751367738289543718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree050.table
  base := (-7774773144087191829968145385679932895107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-288883482953029044612083814813810000000000000)
      constant := (4618323424287119332743440290379375479483511059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67356112214234793479/20000000000000000000)
  centralHi := (84195140267793491849/25000000000000000000)
  directionLo := (340199740721767594157/100000000000000000000)
  directionHi := (170099870360883797079/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree051.table
  base := (-3906648997764063481995578593791085566031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-582874695661504106471290088358880000000000000)
      constant := (9404848289646634846946665152871018538060529788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree051.table
  base := (-1953404216762405078062611282273462999377/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-294438433286140842171166304493890000000000000)
      constant := (4803090600044509227211750692191227588173000196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340199740721767594157/100000000000000000000)
  centralHi := (170099870360883797079/50000000000000000000)
  directionLo := (343584896144899032713/100000000000000000000)
  directionHi := (171792448072449516357/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree052.table
  base := (-1569660683123185835562724304447585326433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-593866906702026180454728743785140000000000000)
      constant := (9773780513062143772661658388513231297263479210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree052.table
  base := (-3924283414886150253680948276425901507187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-299993383619252639730248794173970000000000000)
      constant := (4991467946029478155388015413257754997328364038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (343584896144899032713/100000000000000000000)
  centralHi := (171792448072449516357/50000000000000000000)
  directionLo := (346937023291899782387/100000000000000000000)
  directionHi := (86734255822974945597/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree053.table
  base := (-984928219842252317263088246034407010639/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7420000000000000000000000000000000000000000
      center := (14477)
      previous := (0)
      next := (8525)
      square := (164765475982129588616853507460000000000000)
      linear := (-11412436183821665178078630173800000000000000)
      constant := (191505353221503059032568754538174759984846896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree053.table
  base := (-7879643280179036607960172399177956574283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3710000000000000000000000000000000000000000
      center := (7316)
      previous := (0)
      next := (4185)
      square := (82382737991064794308426753730000000000000)
      linear := (-5765062904761593156402477053850000000000000)
      constant := (97801038945416987838339747819784978110941007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346937023291899782387/100000000000000000000)
  centralHi := (86734255822974945597/25000000000000000000)
  directionLo := (437821338066374131/125000000000000000)
  directionHi := (350257070453099304801/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree054.table
  base := (-3953341527075659749136518132453621611733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-615851328783070328421606054637660000000000000)
      constant := (10532857203660632104085374343080817752993976084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree054.table
  base := (-7906862614575084039585139057379103262743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-311103284285476234848413773534130000000000000)
      constant := (5379051631876825589911333962950834692544684391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437821338066374131/125000000000000000)
  centralHi := (350257070453099304801/100000000000000000000)
  directionLo := (88386485347779034753/25000000000000000000)
  directionHi := (353545941391116139013/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree055.table
  base := (-3965044969453768008356157185401510724263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-626843539823592402405044710063920000000000000)
      constant := (10923000386208358388871558722959275378515266524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree055.table
  base := (-991279764046540547147469835780959608527/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-316658234618588032407496263214210000000000000)
      constant := (5578257388225578031417893933836111929740268792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88386485347779034753/25000000000000000000)
  centralHi := (353545941391116139013/100000000000000000000)
  directionLo := (356804498214181271121/100000000000000000000)
  directionHi := (178402249107090635561/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree056.table
  base := (-7949658298042870900868013429836124537987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-637835750864114476388483365490180000000000000)
      constant := (11320212800991907271479096453302664566419123238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree056.table
  base := (-3974890265298086858785957673025617407927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-322213184951699829966578752894290000000000000)
      constant := (5781072121637966923239759862827394569815862798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356804498214181271121/100000000000000000000)
  centralHi := (178402249107090635561/50000000000000000000)
  directionLo := (45004195501922520031/12500000000000000000)
  directionHi := (360033564015380160249/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree057.table
  base := (-398269889194407858547917960871308674583/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-648827961904636550371922020916440000000000000)
      constant := (11724494068423716412554885587266833301266978840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree057.table
  base := (-497843661558513021227638867531533728069/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-327768135284811627525661242574370000000000000)
      constant := (5987495660737388127005302259578719236879668048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45004195501922520031/12500000000000000000)
  centralHi := (360033564015380160249/100000000000000000000)
  directionLo := (363233925300707562837/100000000000000000000)
  directionHi := (181616962650353781419/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree058.table
  base := (-7977316237325809644385482507059577995521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-659820172945158624355360676342700000000000000)
      constant := (12135843880153243966989769930053655035748141154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree058.table
  base := (-1994349834748680949608691821838725102849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-333323085617923425084743732254450000000000000)
      constant := (6197527866632229705215689202127380593210720452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363233925300707562837/100000000000000000000)
  centralHi := (181616962650353781419/50000000000000000000)
  directionLo := (366406334226229172689/100000000000000000000)
  directionHi := (36640633422622917269/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree059.table
  base := (-7985420029509536651106589806292805500587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-670812383985680698338799331768960000000000000)
      constant := (12554261985628499200999852378546964130883915638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree059.table
  base := (-3992744259627258902309967323484567954333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-338878035951035222643826221934530000000000000)
      constant := (6411168626722660406486008947964125880627900442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366406334226229172689/100000000000000000000)
  centralHi := (36640633422622917269/10000000000000000000)
  directionLo := (18477575533118943091/5000000000000000000)
  directionHi := (369551510662378861821/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree060.table
  base := (-7989714339066244411860779589664396723319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-681804595026202772322237987195220000000000000)
      constant := (12979748181194800400548347146137057934458757006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree060.table
  base := (-1997442692485763838051297743353967522083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-344432986284147020202908711614610000000000000)
      constant := (6628417849689235586639092673191323746453127884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18477575533118943091/5000000000000000000)
  centralHi := (369551510662378861821/100000000000000000000)
  directionLo := (186335072050720953051/50000000000000000000)
  directionHi := (372670144101441906103/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree061.table
  base := (-7990203376963320895485675834239259634647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-692796806066724846305676642621480000000000000)
      constant := (13412302301251644066372745832301881875607872078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree061.table
  base := (-3995124929632147340630064869748325983227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-349987936617258817761991201294690000000000000)
      constant := (6849275461437760814800451961353277332383614998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186335072050720953051/50000000000000000000)
  centralHi := (372670144101441906103/100000000000000000000)
  directionLo := (375762895422542529467/100000000000000000000)
  directionHi := (93940723855635632367/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree062.table
  base := (-499180660557739044229925900050664668437/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-703789017107246920289115298047740000000000000)
      constant := (13851924211079045195745387141779880979984744608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree062.table
  base := (-1597385769256002616617460336829520848599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-355542886950370615321073690974770000000000000)
      constant := (7073741401817904364091204757270285657769989315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (375762895422542529467/100000000000000000000)
  centralHi := (93940723855635632367/25000000000000000000)
  directionLo := (189415199263467101109/50000000000000000000)
  directionHi := (378830398526934202219/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree063.table
  base := (-7979778703405892692869108689782022796317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-714781228147768994272553953474000000000000000)
      constant := (14298613801018099099122259626186787171512037658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree063.table
  base := (-398990510797545394328245927566572253191/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-361097837283482412880156180654850000000000000)
      constant := (7301815621967884042933618783420809795710107340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189415199263467101109/50000000000000000000)
  centralHi := (378830398526934202219/100000000000000000000)
  directionLo := (95468315463763601127/25000000000000000000)
  directionHi := (381873261855054404509/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree064.table
  base := (-3984435025824439665973661564917452508237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-725773439188291068255992608900260000000000000)
      constant := (14752370981750046922187853083600272525322143476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree064.table
  base := (-7968895988414306613040939721058952429077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-366652787616594210439238670334930000000000000)
      constant := (7533498082165739580275429114515697818387058949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95468315463763601127/25000000000000000000)
  centralHi := (381873261855054404509/100000000000000000000)
  directionLo := (96223017448906847827/25000000000000000000)
  directionHi := (384892069795627391309/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree065.table
  base := (-7954166465060804610103085694096877471741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-736765650228813142239431264326520000000000000)
      constant := (15213195680466416871004600204349121196546313434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree065.table
  base := (-3977093903707734281328898070345139736031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-372207737949706007998321160015010000000000000)
      constant := (7768788750090507942497935130837007034740844894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96223017448906847827/25000000000000000000)
  centralHi := (384892069795627391309/100000000000000000000)
  directionLo := (387887383996057888217/100000000000000000000)
  directionHi := (193943691998028944109/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree066.table
  base := (-7935669454225633720686587061978337850177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-747757861269335216222869919752780000000000000)
      constant := (15681087837761983930378811389774839885703939298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree066.table
  base := (-3967843505935490700523362746929337422027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-377762688282817805557403649695090000000000000)
      constant := (8007687599415072266331829805811456876541366198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387887383996057888217/100000000000000000000)
  centralHi := (193943691998028944109/50000000000000000000)
  directionLo := (195429872291218841107/50000000000000000000)
  directionHi := (78171948916487536443/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree067.table
  base := (-7913380253000953912189591010495379182717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-758750072309857290206308575179040000000000000)
      constant := (16156047405114064624176299537582493718260471258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree067.table
  base := (-7913394693783399688203178294124959061897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-383317638615929603116486139375170000000000000)
      constant := (8250194608667386321463922595990900929965919289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195429872291218841107/50000000000000000000)
  centralHi := (78171948916487536443/20000000000000000000)
  directionLo := (24613104456041899577/6250000000000000000)
  directionHi := (393809671296670393233/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree068.table
  base := (-1971824967630307907809062480850584839361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-769742283350379364189747230605300000000000000)
      constant := (16638074342837436924917123231128559602429157256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree068.table
  base := (-1577462349022370099589153561806431702593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-388872588949041400675568629055250000000000000)
      constant := (8496309760308857792241718108695640667159569205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24613104456041899577/6250000000000000000)
  centralHi := (393809671296670393233/100000000000000000000)
  directionLo := (4959220806968676703/1250000000000000000)
  directionHi := (396737664557494136241/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree069.table
  base := (-7857429133390214718488073930058643772011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-780734494390901438173185886031560000000000000)
      constant := (17127168618425081845019427923065848775021895414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree069.table
  base := (-7857438895706181871955248038253174635321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-394427539282153198234651118735330000000000000)
      constant := (8746033039988449116621647678030107827145683177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4959220806968676703/1250000000000000000)
  centralHi := (396737664557494136241/100000000000000000000)
  directionLo := (99911051612883990067/25000000000000000000)
  directionHi := (399644206451535960269/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree070.table
  base := (-1955942179978704582001955985106077814873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-791726705431423512156624541457820000000000000)
      constant := (17623330205201901639134541477849273535409217608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree070.table
  base := (-7823776744009969932670414724650955104673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-399982489615264995793733608415410000000000000)
      constant := (8999364435938964257308197263302388269776814801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99911051612883990067/25000000000000000000)
  centralHi := (399644206451535960269/100000000000000000000)
  directionLo := (201264880829978044367/50000000000000000000)
  directionHi := (80505952331991217747/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree071.table
  base := (-7786319187883041355260964809378826661109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-802718916471945586140063196884080000000000000)
      constant := (18126559081232325462699389024595843262725227466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree071.table
  base := (-77863257819122190793131803509618271459/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-405537439948376793352816098095490000000000000)
      constant := (9256303938488389720799466399364437592830168300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201264880829978044367/50000000000000000000)
  centralHi := (80505952331991217747/20000000000000000000)
  directionLo := (81078955665145123451/20000000000000000000)
  directionHi := (50674347290715702157/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree072.table
  base := (-3872540498552362168381439039934427231839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-813711127512467660123501852310340000000000000)
      constant := (18636855228433871526774966668747637429361398972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree072.table
  base := (-1936271603716058119826800714930900224227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-411092390281488590911898587775570000000000000)
      constant := (9516851539664336532914403700092134835564097996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree072.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81078955665145123451/20000000000000000000)
  centralHi := (50674347290715702157/12500000000000000000)
  directionLo := (102059922216530278247/25000000000000000000)
  directionHi := (408239688866121112989/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree073.table
  base := (-1925013631925951462396771136145635618919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-824703338552989734106940507736600000000000000)
      constant := (19154218631857785822879281131611401934601565624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree073.table
  base := (-1540011795633007927287849046343180059617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-416647340614600388470981077455650000000000000)
      constant := (9781007232873819876520050044994410252438754645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree073.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102059922216530278247/25000000000000000000)
  centralHi := (408239688866121112989/100000000000000000000)
  directionLo := (411064910734607130549/100000000000000000000)
  directionHi := (8221298214692142611/2000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree074.table
  base := (-3825620047482021908308461771258212867277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-835695549593511808090379163162860000000000000)
      constant := (19678649279105219286937022210341759041562929396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree074.table
  base := (-765124375014634988024431173103122626253/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-422202290947712186030063567135730000000000000)
      constant := (10048771012644003351069758645226412997999872610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree074.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411064910734607130549/100000000000000000000)
  centralHi := (8221298214692142611/2000000000000000000)
  directionLo := (103467711783976866899/25000000000000000000)
  directionHi := (413870847135907467597/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree075.table
  base := (-1519727592275746604729058389170206539421/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 393260000000000000000000000000000000000000000
      center := (767281)
      previous := (0)
      next := (451825)
      square := (8732570227052868196693235895380000000000000)
      linear := (-846687760634033882073817818589120000000000000)
      constant := (20210147159853360608202098442543337288153648770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree075.table
  base := (-1519728192569698416381001163117548783911/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (387748)
      previous := (0)
      next := (221805)
      square := (4366285113526434098346617947690000000000000)
      linear := (-427757241280823983589146056815810000000000000)
      constant := (10320142874412277969969465968995098191309790035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree075.checked
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
end ForestUnimodality.Stage170KernelData.Cell419.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell419
open FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem degreePropagationThreshold : row.degreePropagationCheck 75 interval.lo interval.hi = true := by
  decide +kernel

theorem degreePropagationTail (n : ℕ) (hn : 75 ≤ n) (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q :=
  row.degreePropagationCheck_sound 75 interval.lo interval.hi degreePropagationThreshold
    (fun _q hq j => Kernel075.actual_residual_nonneg j hq) n hn q hq j
end ForestUnimodality.Stage170KernelData.Cell419

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel076
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  degreePropagationTail 76 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel077
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  degreePropagationTail 77 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel078
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  degreePropagationTail 78 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel079
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  degreePropagationTail 79 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel080
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  degreePropagationTail 80 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel081
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  degreePropagationTail 81 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel082
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  degreePropagationTail 82 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel083
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  degreePropagationTail 83 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel084
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  degreePropagationTail 84 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel085
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  degreePropagationTail 85 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel086
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  degreePropagationTail 86 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel087
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  degreePropagationTail 87 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel088
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  degreePropagationTail 88 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel089
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  degreePropagationTail 89 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel090
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  degreePropagationTail 90 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel091
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  degreePropagationTail 91 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel092
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  degreePropagationTail 92 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel093
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  degreePropagationTail 93 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel094
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  degreePropagationTail 94 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel095
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  degreePropagationTail 95 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel096
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  degreePropagationTail 96 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel097
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  degreePropagationTail 97 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel098
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  degreePropagationTail 98 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel099
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  degreePropagationTail 99 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel099

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel100
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  degreePropagationTail 100 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel100

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel101
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  degreePropagationTail 101 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel101

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel102
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  degreePropagationTail 102 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel102

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel103
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  degreePropagationTail 103 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel103

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel104
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  degreePropagationTail 104 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel104

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel105
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  degreePropagationTail 105 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel105

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel106
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  degreePropagationTail 106 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel106

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel107
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  degreePropagationTail 107 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel107

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel108
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  degreePropagationTail 108 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel108

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel109
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  degreePropagationTail 109 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel109

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel110
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  degreePropagationTail 110 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel110

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel111
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  degreePropagationTail 111 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel111

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel112
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  degreePropagationTail 112 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel112

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel113
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  degreePropagationTail 113 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel113

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel114
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  degreePropagationTail 114 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel114

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel115
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  degreePropagationTail 115 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel115

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel116
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  degreePropagationTail 116 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel116

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel117
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  degreePropagationTail 117 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel117

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel118
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  degreePropagationTail 118 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel118

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel119
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  degreePropagationTail 119 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel119

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel120
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  degreePropagationTail 120 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel120

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel121
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  degreePropagationTail 121 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel121

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel122
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  degreePropagationTail 122 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel122

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel123
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  degreePropagationTail 123 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel123

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel124
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  degreePropagationTail 124 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel124

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel125
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  degreePropagationTail 125 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel125

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel126
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  degreePropagationTail 126 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel126

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel127
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  degreePropagationTail 127 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel127

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel128
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  degreePropagationTail 128 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel128

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel129
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  degreePropagationTail 129 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel129

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel130
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  degreePropagationTail 130 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel130

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel131
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  degreePropagationTail 131 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel131

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel132
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  degreePropagationTail 132 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel132

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel133
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  degreePropagationTail 133 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel133

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel134
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  degreePropagationTail 134 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel134

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel135
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  degreePropagationTail 135 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel135

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel136
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  degreePropagationTail 136 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel136

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel137
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  degreePropagationTail 137 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel137

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel138
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  degreePropagationTail 138 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel138

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel139
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  degreePropagationTail 139 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel139

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel140
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  degreePropagationTail 140 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel140

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel141
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  degreePropagationTail 141 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel141

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel142
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  degreePropagationTail 142 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel142

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel143
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  degreePropagationTail 143 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel143

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel144
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  degreePropagationTail 144 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel144

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel145
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  degreePropagationTail 145 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel145

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel146
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  degreePropagationTail 146 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel146

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel147
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  degreePropagationTail 147 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel147

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel148
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  degreePropagationTail 148 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel148

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel149
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  degreePropagationTail 149 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel149

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel150
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  degreePropagationTail 150 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel151
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  degreePropagationTail 151 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel152
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  degreePropagationTail 152 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel153
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  degreePropagationTail 153 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel154
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  degreePropagationTail 154 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel155
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  degreePropagationTail 155 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel156
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  degreePropagationTail 156 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel157
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  degreePropagationTail 157 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel158
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  degreePropagationTail 158 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel159
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  degreePropagationTail 159 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel160
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  degreePropagationTail 160 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel161
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  degreePropagationTail 161 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel162
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  degreePropagationTail 162 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel163
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  degreePropagationTail 163 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel164
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  degreePropagationTail 164 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel165
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  degreePropagationTail 165 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel166
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  degreePropagationTail 166 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel167
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  degreePropagationTail 167 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel168
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  degreePropagationTail 168 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel169
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  degreePropagationTail 169 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel170
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  degreePropagationTail 170 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel171
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  degreePropagationTail 171 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel172
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  degreePropagationTail 172 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel173
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  degreePropagationTail 173 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel174
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  degreePropagationTail 174 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel175
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  degreePropagationTail 175 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel176
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  degreePropagationTail 176 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel177
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  degreePropagationTail 177 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel178
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  degreePropagationTail 178 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel179
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  degreePropagationTail 179 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel180
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  degreePropagationTail 180 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel181
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  degreePropagationTail 181 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel182
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  degreePropagationTail 182 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel183
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  degreePropagationTail 183 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel184
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  degreePropagationTail 184 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel185
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  degreePropagationTail 185 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel186
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  degreePropagationTail 186 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel187
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  degreePropagationTail 187 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel188
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  degreePropagationTail 188 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel189
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  degreePropagationTail 189 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel190
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  degreePropagationTail 190 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel191
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  degreePropagationTail 191 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel192
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  degreePropagationTail 192 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel193
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  degreePropagationTail 193 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel194
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  degreePropagationTail 194 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel195
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  degreePropagationTail 195 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel196
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  degreePropagationTail 196 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel197
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  degreePropagationTail 197 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel198
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  degreePropagationTail 198 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel199
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  degreePropagationTail 199 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel199

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel200
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  degreePropagationTail 200 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel201
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  degreePropagationTail 201 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel202
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  degreePropagationTail 202 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel203
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  degreePropagationTail 203 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel204
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  degreePropagationTail 204 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel205
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  degreePropagationTail 205 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel206
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  degreePropagationTail 206 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel207
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  degreePropagationTail 207 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel208
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  degreePropagationTail 208 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel209
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  degreePropagationTail 209 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel210
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  degreePropagationTail 210 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel211
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  degreePropagationTail 211 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel212
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  degreePropagationTail 212 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel213
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  degreePropagationTail 213 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel214
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  degreePropagationTail 214 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel215
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  degreePropagationTail 215 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel216
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  degreePropagationTail 216 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel217
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  degreePropagationTail 217 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel218
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  degreePropagationTail 218 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel219
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  degreePropagationTail 219 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel220
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  degreePropagationTail 220 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel221
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  degreePropagationTail 221 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel222
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  degreePropagationTail 222 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel223
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  degreePropagationTail 223 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel224
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  degreePropagationTail 224 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel225
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  degreePropagationTail 225 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel226
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  degreePropagationTail 226 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel227
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  degreePropagationTail 227 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel228
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  degreePropagationTail 228 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel229
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  degreePropagationTail 229 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel230
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  degreePropagationTail 230 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel231
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  degreePropagationTail 231 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel232
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  degreePropagationTail 232 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel233
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  degreePropagationTail 233 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel234
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  degreePropagationTail 234 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel235
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  degreePropagationTail 235 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel236
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  degreePropagationTail 236 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel237
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  degreePropagationTail 237 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel238
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  degreePropagationTail 238 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel239
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  degreePropagationTail 239 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel240
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  degreePropagationTail 240 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel241
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  degreePropagationTail 241 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel242
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  degreePropagationTail 242 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel243
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  degreePropagationTail 243 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel244
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  degreePropagationTail 244 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel245
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  degreePropagationTail 245 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel246
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  degreePropagationTail 246 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel247
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  degreePropagationTail 247 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel248
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  degreePropagationTail 248 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel249
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  degreePropagationTail 249 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel249

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel250
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  degreePropagationTail 250 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel251
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  degreePropagationTail 251 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel252
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  degreePropagationTail 252 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel253
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  degreePropagationTail 253 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel254
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  degreePropagationTail 254 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel255
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  degreePropagationTail 255 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel256
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  degreePropagationTail 256 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel257
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  degreePropagationTail 257 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel258
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  degreePropagationTail 258 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel259
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  degreePropagationTail 259 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel260
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  degreePropagationTail 260 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel261
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  degreePropagationTail 261 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel262
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  degreePropagationTail 262 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel263
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  degreePropagationTail 263 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel264
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  degreePropagationTail 264 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel265
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  degreePropagationTail 265 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel266
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  degreePropagationTail 266 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel267
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  degreePropagationTail 267 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel268
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  degreePropagationTail 268 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel269
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  degreePropagationTail 269 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel270
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  degreePropagationTail 270 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel271
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  degreePropagationTail 271 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel272
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  degreePropagationTail 272 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel273
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  degreePropagationTail 273 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel274
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  degreePropagationTail 274 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel275
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  degreePropagationTail 275 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel276
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  degreePropagationTail 276 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel277
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  degreePropagationTail 277 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel278
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  degreePropagationTail 278 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel279
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  degreePropagationTail 279 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel280
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  degreePropagationTail 280 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel281
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  degreePropagationTail 281 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel282
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  degreePropagationTail 282 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel283
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  degreePropagationTail 283 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel284
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  degreePropagationTail 284 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel285
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  degreePropagationTail 285 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel286
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  degreePropagationTail 286 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel287
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  degreePropagationTail 287 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel288
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  degreePropagationTail 288 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel289
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  degreePropagationTail 289 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel290
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  degreePropagationTail 290 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel291
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  degreePropagationTail 291 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel292
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  degreePropagationTail 292 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel293
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  degreePropagationTail 293 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel294
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  degreePropagationTail 294 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel295
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  degreePropagationTail 295 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel296
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  degreePropagationTail 296 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel297
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  degreePropagationTail 297 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel298
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  degreePropagationTail 298 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel299
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  degreePropagationTail 299 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel299

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel300
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  degreePropagationTail 300 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel301
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  degreePropagationTail 301 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel302
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  degreePropagationTail 302 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel303
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  degreePropagationTail 303 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel304
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  degreePropagationTail 304 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel305
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  degreePropagationTail 305 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel306
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  degreePropagationTail 306 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel307
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  degreePropagationTail 307 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel308
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  degreePropagationTail 308 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel309
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  degreePropagationTail 309 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel310
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  degreePropagationTail 310 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel311
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  degreePropagationTail 311 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel312
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  degreePropagationTail 312 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel313
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  degreePropagationTail 313 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel314
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  degreePropagationTail 314 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel315
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  degreePropagationTail 315 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel316
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  degreePropagationTail 316 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel317
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  degreePropagationTail 317 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel318
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  degreePropagationTail 318 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel319
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  degreePropagationTail 319 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel320
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  degreePropagationTail 320 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel321
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  degreePropagationTail 321 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel322
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  degreePropagationTail 322 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel323
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  degreePropagationTail 323 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel324
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  degreePropagationTail 324 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel325
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  degreePropagationTail 325 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel326
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  degreePropagationTail 326 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel327
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  degreePropagationTail 327 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel328
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  degreePropagationTail 328 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel329
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  degreePropagationTail 329 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel330
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  degreePropagationTail 330 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel331
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  degreePropagationTail 331 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel332
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  degreePropagationTail 332 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel333
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  degreePropagationTail 333 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel334
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  degreePropagationTail 334 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel335
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  degreePropagationTail 335 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel336
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  degreePropagationTail 336 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel337
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  degreePropagationTail 337 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel338
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  degreePropagationTail 338 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel339
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  degreePropagationTail 339 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel340
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  degreePropagationTail 340 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel341
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  degreePropagationTail 341 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel342
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  degreePropagationTail 342 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel343
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  degreePropagationTail 343 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel344
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  degreePropagationTail 344 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel345
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  degreePropagationTail 345 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel346
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  degreePropagationTail 346 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel347
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  degreePropagationTail 347 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel348
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  degreePropagationTail 348 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell419.Kernel349
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 75 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  degreePropagationTail 349 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell419.Kernel349

