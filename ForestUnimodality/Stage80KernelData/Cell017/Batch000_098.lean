import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell017.Parameters
import ForestUnimodality.BinomialMassData.Q97_255.Batch000_049
import ForestUnimodality.BinomialMassData.Q97_255.Batch050_099
import ForestUnimodality.BinomialMassData.Q33_85.Batch000_049
import ForestUnimodality.BinomialMassData.Q33_85.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree000.table
  base := (1070370212330169678137892223/100000000000000000000000000)
  polynomial :=
    { denominator := 637500000000000000000000000000000000000000
      center := (1106)
      previous := (679)
      next := (0)
      square := (29317948071165627049045054950000000000000)
      linear := (77078323330180992419002894125000000000000)
      constant := (6823610103604831698129062921625000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree000.table
  base := (1070370212330169678137892223/100000000000000000000000000)
  polynomial :=
    { denominator := 212500000000000000000000000000000000000000
      center := (364)
      previous := (231)
      next := (0)
      square := (9772649357055209016348351650000000000000)
      linear := (25692774443393664139667631375000000000000)
      constant := (2274536701201610566043020973875000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree001.table
  base := (70682515993018860191567367440617839292579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (11173832418712017135464797873260000000000000)
      constant := (914110262436910890242064369128662999999989895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree001.table
  base := (69941350884355568097187357533245290272971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (1231112776098254125434205966380000000000000)
      constant := (100487126689880750203560773037327444444443095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24274161358327800397/50000000000000000000)
  directionHi := (9709664543331120159/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree002.table
  base := (23433634409299940113310728645164967320261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (112812)
      previous := (69258)
      next := (0)
      square := (2990430703258893959002595604900000000000000)
      linear := (3311843439033555908726502672510000000000000)
      constant := (300503977278768993086782161741326399999994305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree002.table
  base := (22953639490424688023748997034606689734717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (357558445022869544685506499630000000000000)
      constant := (32690047632943175533854608986882666666666065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24274161358327800397/50000000000000000000)
  centralHi := (9709664543331120159/20000000000000000000)
  directionLo := (68657696416360172759/100000000000000000000)
  directionHi := (1716442410409004319/2500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree003.table
  base := (7786317448026678939040010454002511628529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10837500000000000000000000000000000000000000
      center := (18802)
      previous := (11543)
      next := (0)
      square := (498405117209815659833765934150000000000000)
      linear := (172795111451850541620101068065000000000000)
      constant := (32907431543182135794643824282721887909673215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree003.table
  base := (377584237757110457861090675089335002539/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (6188)
      previous := (3927)
      next := (0)
      square := (166135039069938553277921978050000000000000)
      linear := (49780250998306013326955008035000000000000)
      constant := (10628836328609528514147701866554781573377100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68657696416360172759/100000000000000000000)
  centralHi := (1716442410409004319/2500000000000000000)
  directionLo := (84088161567497804129/100000000000000000000)
  directionHi := (8408816156749780413/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree004.table
  base := (20652929395031931019666833347088526722611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-2476604203222698818570579711460000000000000)
      constant := (258512952630664618263034751702934290027556055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree004.table
  base := (19830628282304789853715933458035464902747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-316874882059290982755372934980000000000000)
      constant := (27544723403388802988066891895069246784469415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84088161567497804129/100000000000000000000)
  centralHi := (8408816156749780413/10000000000000000000)
  directionLo := (24274161358327800397/25000000000000000000)
  directionHi := (97096645433311201589/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree005.table
  base := (13543513784885435703691556508090753914591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-7026749743867604136582372239700000000000000)
      constant := (167862503273391327829070073155420254659255955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree005.table
  base := (12861062590727459900333766799165170350823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-832870768111806018818565902100000000000000)
      constant := (17696886899386891799852837435493671156939235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24274161358327800397/25000000000000000000)
  centralHi := (97096645433311201589/100000000000000000000)
  directionLo := (21711469957607836989/20000000000000000000)
  directionHi := (54278674894019592473/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree006.table
  base := (8639510174664701559650274211307465322449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (75208)
      previous := (46172)
      next := (0)
      square := (1993620468839262639335063736600000000000000)
      linear := (-3858965094837503151531388255980000000000000)
      constant := (35874758883799292786999251308153862172816415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree006.table
  base := (8088782431671023461649551217004574839463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-1348866654164321054881758869220000000000000)
      constant := (11224455804462765813201856021939610643024035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21711469957607836989/20000000000000000000)
  centralHi := (54278674894019592473/50000000000000000000)
  directionLo := (29729654630943862437/25000000000000000000)
  directionHi := (118918618523775449749/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree007.table
  base := (2591361353467369459277710434165154383009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (112812)
      previous := (69258)
      next := (0)
      square := (2990430703258893959002595604900000000000000)
      linear := (-8063520412578707386302978648090000000000000)
      constant := (33968967819371114606817251766403832751032045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree007.table
  base := (4743918299858935823821594788314556827831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-1864862540216836090944951836340000000000000)
      constant := (7014968683491817916612702825326534616215795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29729654630943862437/25000000000000000000)
  centralHi := (118918618523775449749/100000000000000000000)
  directionLo := (16055848559697300271/12500000000000000000)
  directionHi := (128446788477578402169/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree008.table
  base := (670989960678943204360868859041034570057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-5169296591450580022654437456105000000000000)
      constant := (10610386067748101748409932704076654583591285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree008.table
  base := (2335221085440277208824912606713417700951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-2380858426269351127008144803460000000000000)
      constant := (4358570572739469030839274655932888577874195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16055848559697300271/12500000000000000000)
  centralHi := (128446788477578402169/100000000000000000000)
  directionLo := (137315392832720345519/100000000000000000000)
  directionHi := (1716442410409004319/1250000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree009.table
  base := (826612358374977531311415290617707446013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (75208)
      previous := (46172)
      next := (0)
      square := (1993620468839262639335063736600000000000000)
      linear := (-8409110635482408469543180784220000000000000)
      constant := (9005866531601171049116375515783761778466355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree009.table
  base := (54815147000607059385071254428071591897/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-1448427156160933081535668885290000000000000)
      constant := (1400376078552373678961433444456817251455825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137315392832720345519/100000000000000000000)
  centralHi := (1716442410409004319/1250000000000000000)
  directionLo := (72822484074983401191/50000000000000000000)
  directionHi := (145644968149966802383/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree010.table
  base := (-595089728347846927051997069490528087523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-29777477447092130726641334880900000000000000)
      constant := (18990062990881646841080547023075682221763385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree010.table
  base := (-409809620889764523708042243038710870843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-1706425099187190599567265368850000000000000)
      constant := (1024574235913678417419095121709062791631865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72822484074983401191/50000000000000000000)
  centralHi := (145644968149966802383/100000000000000000000)
  directionLo := (76761638182762525227/50000000000000000000)
  directionHi := (30704655273105010091/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree011.table
  base := (-1715613054628741519414883165713126310919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-34327622987737036044653127409140000000000000)
      constant := (16610195842752395367039571855688792326498405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree011.table
  base := (-474758431783888940747377283319073202439/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (6188)
      previous := (3927)
      next := (0)
      square := (166135039069938553277921978050000000000000)
      linear := (-982211521106724058799430926205000000000000)
      constant := (478636837081448315551242607940939222475645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76761638182762525227/50000000000000000000)
  centralHi := (30704655273105010091/20000000000000000000)
  directionLo := (80508285326117089027/50000000000000000000)
  directionHi := (32203314130446835611/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree012.table
  base := (-52468996980521735548600081664571762569/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (37604)
      previous := (23086)
      next := (0)
      square := (996810234419631319667531868300000000000000)
      linear := (-6479628088063656893777486656230000000000000)
      constant := (3121192786335669985180340522074035231584625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree012.table
  base := (-173469010141455662090455856151761416909/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (6188)
      previous := (3927)
      next := (0)
      square := (166135039069938553277921978050000000000000)
      linear := (-1111210492619852817815229167985000000000000)
      constant := (568382047997301384097096069710819010265980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80508285326117089027/50000000000000000000)
  centralHi := (32203314130446835611/20000000000000000000)
  directionLo := (84088161567497804129/50000000000000000000)
  directionHi := (168176323134995608259/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree013.table
  base := (-3377359001518884813176511409445344969481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-43427914069026846680676712465620000000000000)
      constant := (24576786252489598005618594459095288671899595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree013.table
  base := (-3505303381404637048343929085548728242877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-4960837856531926307324109639060000000000000)
      constant := (3044776757338043086082192428354087689042735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84088161567497804129/50000000000000000000)
  centralHi := (168176323134995608259/100000000000000000000)
  directionLo := (87521733446337483559/50000000000000000000)
  directionHi := (175043466892674967119/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree014.table
  base := (-4016792590166177376475402671728580400251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-47978059609671751998688504993860000000000000)
      constant := (33646010171021291694227152992257811894735745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree014.table
  base := (-2062985222589999369483512623536243092483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-2738416871292220671693651303090000000000000)
      constant := (2087024550887911346487899249514128731362065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87521733446337483559/50000000000000000000)
  centralHi := (175043466892674967119/100000000000000000000)
  directionLo := (181651190308259570081/100000000000000000000)
  directionHi := (90825595154129785041/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree015.table
  base := (-913720120795186640394864570190686529281/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (75208)
      previous := (46172)
      next := (0)
      square := (1993620468839262639335063736600000000000000)
      linear := (-17509401716772219105566765840700000000000000)
      constant := (15195214788853489194271698585216869477834325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree015.table
  base := (-4662928820904774150797356420808474453301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-5992829628636956379450495573300000000000000)
      constant := (5624608315031793545549483717231754414980055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181651190308259570081/100000000000000000000)
  centralHi := (90825595154129785041/50000000000000000000)
  directionLo := (47006711341977590143/25000000000000000000)
  directionHi := (188026845367910360573/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree016.table
  base := (-252567594545893313377403236589920045229/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-14269587672740390658678022512585000000000000)
      constant := (15038550242815248847280185646132449058984275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree016.table
  base := (-5133706337318124701585688649925778932829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-6508825514689471415513688540420000000000000)
      constant := (7371126684577867395153391150585249442062095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47006711341977590143/25000000000000000000)
  centralHi := (188026845367910360573/100000000000000000000)
  directionLo := (24274161358327800397/12500000000000000000)
  directionHi := (194193290866622403177/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree017.table
  base := (-1095625397150737754348813125138218333447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7650000000000000000000000000000000000000000
      center := (13272)
      previous := (8148)
      next := (0)
      square := (351815376853987524588540659400000000000000)
      linear := (-3625205660682733408983757798740000000000000)
      constant := (4540092213561576939472627720222314874565225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree017.table
  base := (-2775317504959875635848747248288796972613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 425000000000000000000000000000000000000000
      center := (728)
      previous := (462)
      next := (0)
      square := (19545298714110418032696703300000000000000)
      linear := (-206612394139470189752261220810000000000000)
      constant := (276346601412264013813512145493452257327895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24274161358327800397/12500000000000000000)
  centralHi := (194193290866622403177/100000000000000000000)
  directionLo := (50042465626836093131/25000000000000000000)
  directionHi := (8006794500293774901/4000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree018.table
  base := (-5858330171078079152966768535321307182923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (75208)
      previous := (46172)
      next := (0)
      square := (1993620468839262639335063736600000000000000)
      linear := (-22059547257417124423578558368940000000000000)
      constant := (32181813883091370745702366827806133362028795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree018.table
  base := (-2961292996999874618136055371145432486427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-3770408643397250743820037237330000000000000)
      constant := (5842881392977466475995603728250850057112985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50042465626836093131/25000000000000000000)
  centralHi := (8006794500293774901/4000000000000000000)
  directionLo := (102986544624540259139/50000000000000000000)
  directionHi := (205973089249080518279/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree019.table
  base := (-6198871066758177354968800352226921344609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-70728787312896278588747467635060000000000000)
      constant := (118155963421070753218835117578996887913359955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree019.table
  base := (-125121819319232795147623149017826405759/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-4028406586423508261851633720890000000000000)
      constant := (7115811712994324381477641843765021091956125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102986544624540259139/50000000000000000000)
  centralHi := (205973089249080518279/100000000000000000000)
  directionLo := (42323446520060356179/20000000000000000000)
  directionHi := (6613038518759430653/3125000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree020.table
  base := (-3252470035292132922841611026385350926467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (112812)
      previous := (69258)
      next := (0)
      square := (2990430703258893959002595604900000000000000)
      linear := (-37639466426770591953379630081650000000000000)
      constant := (70972815911337053710374632266458511201296665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree020.table
  base := (-6556072358885359623398396269260144432507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-8572809058899531559766460408900000000000000)
      constant := (17026253452317615243351556060119091295027385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42323446520060356179/20000000000000000000)
  centralHi := (6613038518759430653/3125000000000000000)
  directionLo := (21711469957607836989/10000000000000000000)
  directionHi := (217114699576078369891/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree021.table
  base := (-1695130356302811337824293227876093628413/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10837500000000000000000000000000000000000000
      center := (18802)
      previous := (11543)
      next := (0)
      square := (498405117209815659833765934150000000000000)
      linear := (-6652423199515507435397587724295000000000000)
      constant := (13988552648196432574898816256636134120829645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree021.table
  base := (-6826323423511508165749623220625738096049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-9088804944952046595829653376020000000000000)
      constant := (20064171617621666359269749320703808451209195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21711469957607836989/10000000000000000000)
  centralHi := (217114699576078369891/100000000000000000000)
  directionLo := (222476363712218434273/100000000000000000000)
  directionHi := (111238181856109217137/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree022.table
  base := (-7028736166994557683754934688636520482169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-84379223934830994542782845219780000000000000)
      constant := (195866374210317482888609324927634051129392155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree022.table
  base := (-7069827582574641366940538547087430828607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-9604800831004561631892846343140000000000000)
      constant := (23341066876049368715989126619450662452662885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222476363712218434273/100000000000000000000)
  centralHi := (111238181856109217137/50000000000000000000)
  directionLo := (22771181798319524549/10000000000000000000)
  directionHi := (227711817983195245491/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree023.table
  base := (-906509280619130775247869636018909973611/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-22232342368868974965198659437005000000000000)
      constant := (56481119332891231376845343919151151586377890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree023.table
  base := (-7288973963705147492845896276561145064743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-10120796717057076667956039310260000000000000)
      constant := (26853486938174811269320668386021145381446365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22771181798319524549/10000000000000000000)
  centralHi := (227711817983195245491/100000000000000000000)
  directionLo := (29103697061061992081/12500000000000000000)
  directionHi := (232829576488495936649/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree024.table
  base := (-7452553989309854524331491546703879975397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (75208)
      previous := (46172)
      next := (0)
      square := (1993620468839262639335063736600000000000000)
      linear := (-31159838338706935059602143425420000000000000)
      constant := (86003564252515845332818975797614680306654005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree024.table
  base := (-3742852683989833015257635877496374998499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-5318396301554795852009616138690000000000000)
      constant := (15299312228221124980238869122761738127168945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29103697061061992081/12500000000000000000)
  centralHi := (232829576488495936649/100000000000000000000)
  directionLo := (29729654630943862437/12500000000000000000)
  directionHi := (237837237047550899497/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree025.table
  base := (-7631833582063701549283843805820339547123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-98029660556765710496818222804500000000000000)
      constant := (292103455831371975087060588907806484189665385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree025.table
  base := (-7661621858436997844412149984676214008753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-11152788489162106740082425244500000000000000)
      constant := (34574167339760617540310600369642870757351915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29729654630943862437/12500000000000000000)
  centralHi := (237837237047550899497/100000000000000000000)
  directionLo := (242741613583278003971/100000000000000000000)
  directionHi := (60685403395819500993/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree026.table
  base := (-3895645251996982935328817810925877743529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (112812)
      previous := (69258)
      next := (0)
      square := (2990430703258893959002595604900000000000000)
      linear := (-51289903048705307907415007666370000000000000)
      constant := (164092426207751212080297094640072959945405355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree026.table
  base := (-7818054857036229167693686107194791919807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-11668784375214621776145618211620000000000000)
      constant := (38778191683399034401907165578791525675878885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242741613583278003971/100000000000000000000)
  centralHi := (60685403395819500993/25000000000000000000)
  directionLo := (12377442244221339389/5000000000000000000)
  directionHi := (247548844884426787781/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree027.table
  base := (-63456634855760750917347395418496444033/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (75208)
      previous := (46172)
      next := (0)
      square := (1993620468839262639335063736600000000000000)
      linear := (-35709983879351840377613935953660000000000000)
      constant := (122079955637542244365458134700006239389618125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree027.table
  base := (-7956121364550140498433924355804259883591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-12184780261267136812208811178740000000000000)
      constant := (43209083421240832725550439955914844468211005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12377442244221339389/5000000000000000000)
  centralHi := (247548844884426787781/100000000000000000000)
  directionLo := (252264484702493412387/100000000000000000000)
  directionHi := (63066121175623353097/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree028.table
  base := (-8055174871174624862168757398167386841013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-111680097178700426450853600389220000000000000)
      constant := (406255822956720977896663857343985134132625935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree028.table
  base := (-2019191139228779356953532036540993136287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (6188)
      previous := (3927)
      next := (0)
      square := (166135039069938553277921978050000000000000)
      linear := (-3175194036829912962068001036465000000000000)
      constant := (11966369916014483832995874466346264918065285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252264484702493412387/100000000000000000000)
  centralHi := (63066121175623353097/25000000000000000000)
  directionLo := (256893576955156804337/100000000000000000000)
  directionHi := (128446788477578402169/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree029.table
  base := (-408070229512287824431080970010133923127/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-29057560679836332942216348229365000000000000)
      constant := (112055489585692599610579107708128041648666825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree029.table
  base := (-818078486283706764494892048324227122629/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-6608386016686083442167598556490000000000000)
      constant := (26373111896185152805217854532511459039005475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256893576955156804337/100000000000000000000)
  centralHi := (128446788477578402169/50000000000000000000)
  directionLo := (65360179734785579813/25000000000000000000)
  directionHi := (261440718939142319253/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree030.table
  base := (-4125737113522792225797640538667042011381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (37604)
      previous := (23086)
      next := (0)
      square := (996810234419631319667531868300000000000000)
      linear := (-20130064709998372847812864240950000000000000)
      constant := (82021515879167240009401127473578372880663365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree030.table
  base := (-4134432123972468392848129408645417281863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-6866383959712340960199195040050000000000000)
      constant := (28925165182922058558546162519607372027707965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65360179734785579813/25000000000000000000)
  centralHi := (261440718939142319253/100000000000000000000)
  directionLo := (26591011480952759657/10000000000000000000)
  directionHi := (265910114809527596571/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree031.table
  base := (-4162993853401149190337275471533530854001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (112812)
      previous := (69258)
      next := (0)
      square := (2990430703258893959002595604900000000000000)
      linear := (-62665266900317571202444488986970000000000000)
      constant := (268984689852913748303092212326360431243716995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree031.table
  base := (-4170792770121246989535193814997508670219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-7124381902738598478230791523610000000000000)
      constant := (31588478599006961730263881255962599971533545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26591011480952759657/10000000000000000000)
  centralHi := (265910114809527596571/100000000000000000000)
  directionLo := (135152810548483125033/50000000000000000000)
  directionHi := (270305621096966250067/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree032.table
  base := (-8385463275862535889373992195898173653157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-129880679341280047722900770502180000000000000)
      constant := (585736071841504545927892515869816251640693215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree032.table
  base := (-4199724026316631830245338066171606839289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-7382379845764855996262388007170000000000000)
      constant := (34362691390867065915780516486638028117227395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135152810548483125033/50000000000000000000)
  centralHi := (270305621096966250067/100000000000000000000)
  directionLo := (137315392832720345519/50000000000000000000)
  directionHi := (274630785665440691039/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree033.table
  base := (-2107586658372750956396140465779724667747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10837500000000000000000000000000000000000000
      center := (18802)
      previous := (11543)
      next := (0)
      square := (498405117209815659833765934150000000000000)
      linear := (-11202568740160412753409380252535000000000000)
      constant := (52951947946924756288725761862735893565316755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree033.table
  base := (-8442880378473193947539638631855951803673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-15280755577582227028587968981460000000000000)
      constant := (74494987799605397200285403248900149643692515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137315392832720345519/50000000000000000000)
  centralHi := (274630785665440691039/100000000000000000000)
  directionLo := (139444440615086697689/50000000000000000000)
  directionHi := (278888881230173395379/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree034.table
  base := (-4230510882141465205484178231613260026201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3825000000000000000000000000000000000000000
      center := (6636)
      previous := (4074)
      next := (0)
      square := (175907688426993762294270329700000000000000)
      linear := (-4087675600663819363497775163490000000000000)
      constant := (20206655780910121829232904084667856079956235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree034.table
  base := (-8472250984118671308772280056261882778679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1456)
      previous := (924)
      next := (0)
      square := (39090597428220836065393406600000000000000)
      linear := (-929220674331455415567715408740000000000000)
      constant := (4734425871631925948214052424601739963812285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139444440615086697689/50000000000000000000)
  centralHi := (278888881230173395379/100000000000000000000)
  directionLo := (283082934336244120849/100000000000000000000)
  directionHi := (5661658686724882417/2000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree035.table
  base := (-2119454990124840208647751043680447532791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-35882778990803690919234037021725000000000000)
      constant := (185135131737297713357930702746510779836053045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree035.table
  base := (-8487877052950482309247832536066129952099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-16312747349687257100714354915700000000000000)
      constant := (86695680506160927003110906452684442219216945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283082934336244120849/100000000000000000000)
  centralHi := (5661658686724882417/2000000000000000000)
  directionLo := (143607875263701014507/50000000000000000000)
  directionHi := (57443150105480405803/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree036.table
  base := (-8481027395269416681575420706655901139649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (75208)
      previous := (46172)
      next := (0)
      square := (1993620468839262639335063736600000000000000)
      linear := (-49360420501286556331649313538380000000000000)
      constant := (265320781625430994321199279959542668559621585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree036.table
  base := (-66328374370972678961365503972045050039/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (6188)
      previous := (3927)
      next := (0)
      square := (166135039069938553277921978050000000000000)
      linear := (-4207185808934943034194386970705000000000000)
      constant := (23281478724121128522815895790144636886196640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143607875263701014507/50000000000000000000)
  centralHi := (57443150105480405803/20000000000000000000)
  directionLo := (58257987259986720953/20000000000000000000)
  directionHi := (145644968149966802383/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree037.table
  base := (-1058861439833171301752061397396728578613/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-38157851761126143578239933285845000000000000)
      constant := (213322133061015156854999961142244089670275870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree037.table
  base := (-8478951351467633444984277685800940206197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-17344739121792287172840740849940000000000000)
      constant := (99775602304319231388763721567389641402045335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58257987259986720953/20000000000000000000)
  centralHi := (145644968149966802383/50000000000000000000)
  directionLo := (295307918329698561127/100000000000000000000)
  directionHi := (36913489791212320141/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree038.table
  base := (-527976655369151663833540243516149845739/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-39295388146287369907742881417905000000000000)
      constant := (228129075990967007778872536240947885024657220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree038.table
  base := (-8454838880456040641403891273057349444131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-17860735007844802208903933817060000000000000)
      constant := (106644448626566417987570169722104130053230705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295307918329698561127/100000000000000000000)
  centralHi := (36913489791212320141/12500000000000000000)
  directionLo := (299271960375208645559/100000000000000000000)
  directionHi := (7481799009380216139/2500000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree039.table
  base := (-2102854445445911655745306248207833579679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10837500000000000000000000000000000000000000
      center := (18802)
      previous := (11543)
      next := (0)
      square := (498405117209815659833765934150000000000000)
      linear := (-13477641510482865412415276516655000000000000)
      constant := (81136937317167286799223501214868041432091535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree039.table
  base := (-8417870339638265412965021362965959883723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-18376730893897317244967126784180000000000000)
      constant := (113732199784268632263121660270662187968020265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299271960375208645559/100000000000000000000)
  centralHi := (7481799009380216139/2500000000000000000)
  directionLo := (151592089095556856441/50000000000000000000)
  directionHi := (303184178191113712883/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree040.table
  base := (-4181213086101327401898010836517203831077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (112812)
      previous := (69258)
      next := (0)
      square := (2990430703258893959002595604900000000000000)
      linear := (-83140921833219645133497555364050000000000000)
      constant := (518333636504938106860327995411493764176843615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree040.table
  base := (-8368197736631860486229981077386715702219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-18892726779949832281030319751300000000000000)
      constant := (121038636126418510525535650751976195810293545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151592089095556856441/50000000000000000000)
  centralHi := (303184178191113712883/100000000000000000000)
  directionLo := (76761638182762525227/25000000000000000000)
  directionHi := (307046552731050100909/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree041.table
  base := (-8300791088817033180403309589337041015631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-170831989207084195585006903256340000000000000)
      constant := (1101586566266819513379239378837139781591718845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree041.table
  base := (-8305952565393647600398161812048771589831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-19408722666002347317093512718420000000000000)
      constant := (128563567644248445361669020599217525052694205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76761638182762525227/25000000000000000000)
  centralHi := (307046552731050100909/100000000000000000000)
  directionLo := (155430470936864619373/50000000000000000000)
  directionHi := (310860941873729238747/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree042.table
  base := (-1645326706724385413487159785072344139371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (75208)
      previous := (46172)
      next := (0)
      square := (1993620468839262639335063736600000000000000)
      linear := (-58460711582576366967672898594860000000000000)
      constant := (389466517981963491916544594227620940779133575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree042.table
  base := (-4115624321541544625375975590811196876091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-9962359276027431176578352842770000000000000)
      constant := (68153414935981506732919359854593820514048505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155430470936864619373/50000000000000000000)
  centralHi := (310860941873729238747/100000000000000000000)
  directionLo := (39328636358658600579/12500000000000000000)
  directionHi := (314629090869268804633/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree043.table
  base := (-8140058575450370679439342705358585270937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-179932280288374006221030488312820000000000000)
      constant := (1237104869626915490871670383779783598551464315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree043.table
  base := (-814418454325661221854813704169881706579/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-10220357219053688694609949326330000000000000)
      constant := (72134140185386589069564344815278604669966725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39328636358658600579/12500000000000000000)
  centralHi := (314629090869268804633/100000000000000000000)
  directionLo := (318352641672443398219/100000000000000000000)
  directionHi := (15917632083622169911/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree044.table
  base := (-4020578749223745748012114361067528142297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (112812)
      previous := (69258)
      next := (0)
      square := (2990430703258893959002595604900000000000000)
      linear := (-92241212914509455769521140420530000000000000)
      constant := (653850663079793587936508694691220796509427515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree044.table
  base := (-8044845685159047735883502869289422751701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-20956710324159892425283091619780000000000000)
      constant := (152447795709870158251159078239044784123792055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318352641672443398219/100000000000000000000)
  centralHi := (15917632083622169911/5000000000000000000)
  directionLo := (322033141304468356109/100000000000000000000)
  directionHi := (32203314130446835611/10000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree045.table
  base := (-991251206627482108653960693862835512223/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10837500000000000000000000000000000000000000
      center := (18802)
      previous := (11543)
      next := (0)
      square := (498405117209815659833765934150000000000000)
      linear := (-15752714280805318071421172780775000000000000)
      constant := (115015657632655676861698218489184216109026590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree045.table
  base := (-7933306129429201073543465070300308894643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-21472706210212407461346284586900000000000000)
      constant := (160845268871630880185644958828116053647240865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322033141304468356109/100000000000000000000)
  centralHi := (32203314130446835611/10000000000000000000)
  directionLo := (81418012341029388709/25000000000000000000)
  directionHi := (325672049364117554837/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree046.table
  base := (-7806684051928198505859581335183122649041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-193582716910308722175065865897540000000000000)
      constant := (1454563668412805014426847806036591489949221795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree046.table
  base := (-7809630122762192826914973156363007340769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-21988702096264922497409477554020000000000000)
      constant := (169460607019580894682252189353463454392588795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81418012341029388709/25000000000000000000)
  centralHi := (325672049364117554837/100000000000000000000)
  directionLo := (41158843098951856599/12500000000000000000)
  directionHi := (329270744791614852793/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree047.table
  base := (-7671240747724766748561103786638334886751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-198132862450953627493077658425780000000000000)
      constant := (1530827875638955836426220235691420454797803245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree047.table
  base := (-3836936713808987209359058600506523866417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-11252348991158718766736335260570000000000000)
      constant := (89146864788482785967575119829414073013027435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41158843098951856599/12500000000000000000)
  centralHi := (329270744791614852793/100000000000000000000)
  directionLo := (332830531974194485801/100000000000000000000)
  directionHi := (166415265987097242901/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree048.table
  base := (-7523732022349079408474539503548537022029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (75208)
      previous := (46172)
      next := (0)
      square := (1993620468839262639335063736600000000000000)
      linear := (-67561002663866177603696483651340000000000000)
      constant := (536326611114565719734880831208021092009504285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree048.table
  base := (-7526084467671119288881218597397141783513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-23020693868369952569535863488260000000000000)
      constant := (187344566571575153323642685331113130122823715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (332830531974194485801/100000000000000000000)
  centralHi := (166415265987097242901/50000000000000000000)
  directionLo := (84088161567497804129/25000000000000000000)
  directionHi := (336352646269991216517/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree049.table
  base := (-1472840683035414402105270390483629100079/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-207233153532243438129101243482260000000000000)
      constant := (1689018949287444941260445922452630017767363025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree049.table
  base := (-3683152657581483882327526020954996332459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-11768344877211233802799528227690000000000000)
      constant := (98306528604510451037426078467014030299596745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84088161567497804129/25000000000000000000)
  centralHi := (336352646269991216517/100000000000000000000)
  directionLo := (339838259016589205559/100000000000000000000)
  directionHi := (8495956475414730139/2500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree050.table
  base := (-7192694612008127413835493182366618500941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-211783299072888343447113036010500000000000000)
      constant := (1770944707356378208510788550778322126395262295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree050.table
  base := (-3597286271244915668395807727073969874403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-12026342820237491320831124711250000000000000)
      constant := (103049574321095074042321008736878113531487665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339838259016589205559/100000000000000000000)
  centralHi := (8495956475414730139/2500000000000000000)
  directionLo := (171644241040900431899/50000000000000000000)
  directionHi := (343288482081800863799/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree051.table
  base := (-1752310053561885260531910328022539372331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637500000000000000000000000000000000000000
      center := (1106)
      previous := (679)
      next := (0)
      square := (29317948071165627049045054950000000000000)
      linear := (-1060458061831045337083945237935000000000000)
      constant := (9091944399800103401814303601311252460055595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree051.table
  base := (-3505458978559618171664154754504746948447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 425000000000000000000000000000000000000000
      center := (728)
      previous := (462)
      next := (0)
      square := (19545298714110418032696703300000000000000)
      linear := (-722608280191985225815454187930000000000000)
      constant := (6347141026743891641016124205149096509382005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171644241040900431899/50000000000000000000)
  centralHi := (343288482081800863799/100000000000000000000)
  directionLo := (173352186003398476743/50000000000000000000)
  directionHi := (346704372006796953487/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree052.table
  base := (-1362774080960035395021410457643948465369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-220883590154178154083136621066980000000000000)
      constant := (1940454407367295840281880225534214251039380775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree052.table
  base := (-6815369236173262019462493906163503597009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-25084677412580012713788635356740000000000000)
      constant := (225723956016886000709710588671945737302321995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173352186003398476743/50000000000000000000)
  centralHi := (346704372006796953487/100000000000000000000)
  directionLo := (350086933785349934237/100000000000000000000)
  directionHi := (175043466892674967119/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree053.table
  base := (-3303305762427671977710373883683132384813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (112812)
      previous := (69258)
      next := (0)
      square := (2990430703258893959002595604900000000000000)
      linear := (-112716867847411529700574206797610000000000000)
      constant := (1014018807106717743623975453367126863335506935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree053.table
  base := (-3303975237337670528194063958712208179601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-12800336649316263874925914161930000000000000)
      constant := (117931298573831171295676921708306859180476555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (350086933785349934237/100000000000000000000)
  centralHi := (175043466892674967119/50000000000000000000)
  directionLo := (176718562158753237951/50000000000000000000)
  directionHi := (353437124317506475903/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree054.table
  base := (-3193743286874492365146571860811222072753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (37604)
      previous := (23086)
      next := (0)
      square := (996810234419631319667531868300000000000000)
      linear := (-38330646872577994119860034353910000000000000)
      constant := (352917663165212683240112741425091352314615745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree054.table
  base := (-6388682659460001087866450279511332770223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-26116669184685042785915021290980000000000000)
      constant := (246218687975645449008692997234514124147027765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176718562158753237951/50000000000000000000)
  centralHi := (353437124317506475903/100000000000000000000)
  directionLo := (89188963892831587311/25000000000000000000)
  directionHi := (71351171114265269849/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree055.table
  base := (-1539128910596068193448820272875143889649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-58633506694028217509292999662925000000000000)
      constant := (552214810104655476457440740887933753715114755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree055.table
  base := (-3078792039520300258739575644396045593229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-13316332535368778910989107129050000000000000)
      constant := (128396101036966758534276253823697714117784095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89188963892831587311/25000000000000000000)
  centralHi := (71351171114265269849/20000000000000000000)
  directionLo := (22502749842643329501/6250000000000000000)
  directionHi := (360043997482293272017/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree056.table
  base := (-5913716289231801980684357967139076115803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-239084172316757775355183791179940000000000000)
      constant := (2302097170147562832813893090575564315113981985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree056.table
  base := (-5914670678273699112119718655962495190839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-27148660956790072858041407225220000000000000)
      constant := (267583116402208817907771284913302194449237645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22502749842643329501/6250000000000000000)
  centralHi := (360043997482293272017/100000000000000000000)
  directionLo := (181651190308259570081/50000000000000000000)
  directionHi := (363302380616519140163/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree057.table
  base := (-1414775966669776218512093447824066613147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10837500000000000000000000000000000000000000
      center := (18802)
      previous := (11543)
      next := (0)
      square := (498405117209815659833765934150000000000000)
      linear := (-20302859821450223389432965309015000000000000)
      constant := (199768297376691584994192283072413671232007755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree057.table
  base := (-5659956365413044406925698572000453880301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-27664656842842587894104600192340000000000000)
      constant := (278591410863044686338075574786271344142965055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181651190308259570081/50000000000000000000)
  centralHi := (363302380616519140163/100000000000000000000)
  directionLo := (91632949655210911647/25000000000000000000)
  directionHi := (366531798620843646589/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree058.table
  base := (-1078538360885092656516661850187091090161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-248184463398047585991207376236420000000000000)
      constant := (2494226260883591306996814653597976401862280975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree058.table
  base := (-168545414939996395412255118792213895659/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (6188)
      previous := (3927)
      next := (0)
      square := (166135039069938553277921978050000000000000)
      linear := (-7045163182223775732541948289865000000000000)
      constant := (72454266979394604659085999280420007366181960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91632949655210911647/25000000000000000000)
  centralHi := (366531798620843646589/100000000000000000000)
  directionLo := (184866505240153779163/50000000000000000000)
  directionHi := (369733010480307558327/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree059.table
  base := (-5114491855695904402042173751915650515429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-252734608938692491309219168764660000000000000)
      constant := (2593117094386748215332646973439404965046845855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree059.table
  base := (-1278793003440736297082268879431162052451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (6188)
      previous := (3927)
      next := (0)
      square := (166135039069938553277921978050000000000000)
      linear := (-7174162153736904491557746531645000000000000)
      constant := (75315018063109701672504789505878970834208305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184866505240153779163/50000000000000000000)
  centralHi := (369733010480307558327/100000000000000000000)
  directionLo := (74581348520238424827/20000000000000000000)
  directionHi := (46613342825149015517/12500000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree060.table
  base := (-4824514311255902766390724464021646965491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (75208)
      previous := (46172)
      next := (0)
      square := (1993620468839262639335063736600000000000000)
      linear := (-85761584826445798875743653764300000000000000)
      constant := (897963978399454916207859894800066160404596515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree060.table
  base := (-482512182967849102986048021938637484853/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-14606322250500066501147089546850000000000000)
      constant := (156460205245474173774389405150893344171937075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74581348520238424827/20000000000000000000)
  centralHi := (46613342825149015517/12500000000000000000)
  directionLo := (47006711341977590143/12500000000000000000)
  directionHi := (75210738147164144229/20000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree061.table
  base := (-141336505797717163512127616241039076723/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-65458725004995575486310688455285000000000000)
      constant := (699137666521472354569365100136679294457739080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree061.table
  base := (-1130827704037350748170679373666956980389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (6188)
      previous := (3927)
      next := (0)
      square := (166135039069938553277921978050000000000000)
      linear := (-7432160096763162009589343015205000000000000)
      constant := (81199517735647619608774435812838247163337895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47006711341977590143/12500000000000000000)
  centralHi := (75210738147164144229/20000000000000000000)
  directionLo := (94793630440892768327/25000000000000000000)
  directionHi := (379174521763571073309/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree062.table
  base := (-105231534462922447156030853819089730257/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-66596261390156801815813636587345000000000000)
      constant := (725273296077430020475791828181685380580077150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree062.table
  base := (-4209746047085931496886189641338652328793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-30244636273105163074420565027940000000000000)
      constant := (336893043385564887491945325551937647384894115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94793630440892768327/25000000000000000000)
  centralHi := (379174521763571073309/100000000000000000000)
  directionLo := (76453975068202535359/20000000000000000000)
  directionHi := (95567468835253169199/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree063.table
  base := (-971000204193575372400137557227093252909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10837500000000000000000000000000000000000000
      center := (18802)
      previous := (11543)
      next := (0)
      square := (498405117209815659833765934150000000000000)
      linear := (-22577932591772676048438861573135000000000000)
      constant := (250626616649174400902953108417781550748639485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree063.table
  base := (-776886742131196792541237912557661773139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-30760632159157678110483757995060000000000000)
      constant := (349205318877968948497081558958142893689070725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76453975068202535359/20000000000000000000)
  centralHi := (95567468835253169199/25000000000000000000)
  directionLo := (192670182716367603253/50000000000000000000)
  directionHi := (385340365432735206507/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree064.table
  base := (-44337407201765239375860074515251526947/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-68871334160479254474819532851465000000000000)
      constant := (778957308377670406594974072341655077841085300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree064.table
  base := (-3547379222807708300188455316795412318993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-31276628045210193146546950962180000000000000)
      constant := (361734889593757587720490351976478629199055115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192670182716367603253/50000000000000000000)
  centralHi := (385340365432735206507/100000000000000000000)
  directionLo := (388386581733244806353/100000000000000000000)
  directionHi := (194193290866622403177/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree065.table
  base := (-1599120994352165708263818753855101124811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (112812)
      previous := (69258)
      next := (0)
      square := (2990430703258893959002595604900000000000000)
      linear := (-140017741091280961608644961967050000000000000)
      constant := (1613011308063849623999169299775764409871832945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree065.table
  base := (-1599293662970871820935815235077932103727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-15896311965631354091305071964650000000000000)
      constant := (187240874340080940807826682326462388110114485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388386581733244806353/100000000000000000000)
  centralHi := (194193290866622403177/50000000000000000000)
  directionLo := (19570454549462755551/5000000000000000000)
  directionHi := (391409090989255111021/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree066.table
  base := (-2837753736021162423567110585998473964437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (75208)
      previous := (46172)
      next := (0)
      square := (1993620468839262639335063736600000000000000)
      linear := (-94861875907735609511767238820780000000000000)
      constant := (1112699828919163358106806808970152615364165605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree066.table
  base := (-709515543679068422792603054156327094293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (6188)
      previous := (3927)
      next := (0)
      square := (166135039069938553277921978050000000000000)
      linear := (-8077154954328805804668334224105000000000000)
      constant := (96861472533425188682784089885626107348746615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19570454549462755551/5000000000000000000)
  centralHi := (391409090989255111021/100000000000000000000)
  directionLo := (98602109557692630027/25000000000000000000)
  directionHi := (394408438230770520109/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree067.table
  base := (-2465531930419537583742875522731774435151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-289135773263851733853313508990580000000000000)
      constant := (3452059791919230735855855538945365273470861245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree067.table
  base := (-2465807410697638092855617647093378715329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-32824615703367738254736529863540000000000000)
      constant := (400627308692310846280245505948882067756349595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98602109557692630027/25000000000000000000)
  centralHi := (394408438230770520109/100000000000000000000)
  directionLo := (397385147918535152509/100000000000000000000)
  directionHi := (39738514791853515251/10000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree068.table
  base := (-1040790092963943980048576177347680645327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3825000000000000000000000000000000000000000
      center := (6636)
      previous := (4074)
      next := (0)
      square := (175907688426993762294270329700000000000000)
      linear := (-8637821141308724681509567691730000000000000)
      constant := (104938337782720043724405290119937024306324845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree068.table
  base := (-2081826227336494294331566933541556023043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1456)
      previous := (924)
      next := (0)
      square := (39090597428220836065393406600000000000000)
      linear := (-1961212446436485487694101342980000000000000)
      constant := (24354470573026820955969503601384967738041345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (397385147918535152509/100000000000000000000)
  centralHi := (39738514791853515251/10000000000000000000)
  directionLo := (50042465626836093131/12500000000000000000)
  directionHi := (400339725014688745049/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree069.table
  base := (-67436067207452961245662460996671157651/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (75208)
      previous := (46172)
      next := (0)
      square := (1993620468839262639335063736600000000000000)
      linear := (-99412021448380514829779031349020000000000000)
      constant := (1228543507837344229956383259482121763289572875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree069.table
  base := (-843060713274520723408004119425247127369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-16928303737736384163431457898890000000000000)
      constant := (213820979616183588435667439635564517900951795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50042465626836093131/12500000000000000000)
  centralHi := (400339725014688745049/100000000000000000000)
  directionLo := (201636327991409536307/50000000000000000000)
  directionHi := (80654531196563814523/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree070.table
  base := (-1278499208508974203041782513481960431237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-302786209885786449807348886575300000000000000)
      constant := (3805240872264824105651780620412367104591762815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree070.table
  base := (-1278695468010054409451108323261425702603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-34372603361525283362926108764900000000000000)
      constant := (441475183610814458468345029123087239859738665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201636327991409536307/50000000000000000000)
  centralHi := (80654531196563814523/20000000000000000000)
  directionLo := (203092204861509688259/50000000000000000000)
  directionHi := (406184409723019376519/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree071.table
  base := (-429687615556498254945132450919773291417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (112812)
      previous := (69258)
      next := (0)
      square := (2990430703258893959002595604900000000000000)
      linear := (-153668177713215677562680339551770000000000000)
      constant := (1963367249437865796872150041584562348345121915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree071.table
  base := (-214887628028880617469228296492970822533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (6188)
      previous := (3927)
      next := (0)
      square := (166135039069938553277921978050000000000000)
      linear := (-8722149811894449599747325433005000000000000)
      constant := (113881417438756399130468036077644657161439815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203092204861509688259/50000000000000000000)
  centralHi := (406184409723019376519/100000000000000000000)
  directionLo := (81815087689408049933/20000000000000000000)
  directionHi := (204537719223520124833/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree072.table
  base := (-4285319143955587192477158739442677511/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10837500000000000000000000000000000000000000
      center := (18802)
      previous := (11543)
      next := (0)
      square := (498405117209815659833765934150000000000000)
      linear := (-25990541747256355036947705969315000000000000)
      constant := (337509281264229998944131764149108899824745375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree072.table
  base := (-428688457444197508416054950233334624647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-35404595133630313435052494699140000000000000)
      constant := (469793414921554294564850021415504831467385085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81815087689408049933/20000000000000000000)
  centralHi := (204537719223520124833/50000000000000000000)
  directionLo := (411946178498161036557/100000000000000000000)
  directionHi := (205973089249080518279/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree073.table
  base := (14028832975949995587246272615369991643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-316436646507721165761384264160020000000000000)
      constant := (4175371476327689890208875349312774886741317215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree073.table
  base := (2777805312707489062301836201957885993/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-35920591019682828471115687666260000000000000)
      constant := (484278416698059199119477822279611145726299425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411946178498161036557/100000000000000000000)
  centralHi := (205973089249080518279/50000000000000000000)
  directionLo := (414797051119989632671/100000000000000000000)
  directionHi := (12962407847499676021/3125000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree074.table
  base := (468305328495649796181392480183558359267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-320986792048366071079396056688260000000000000)
      constant := (4302514780465532335083358477844715176462267335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree074.table
  base := (468180471086824160363385156990990921149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-36436586905735343507178880633380000000000000)
      constant := (498980672962094170042043787499539981881060305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414797051119989632671/100000000000000000000)
  centralHi := (12962407847499676021/3125000000000000000)
  directionLo := (417628463178026014719/100000000000000000000)
  directionHi := (40784029607229103/9765625000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree075.table
  base := (18685921763899951382570851747151083753/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (37604)
      previous := (23086)
      next := (0)
      square := (996810234419631319667531868300000000000000)
      linear := (-54256156264835162732901308202750000000000000)
      constant := (738590211380879403127197197064347498701731375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree075.table
  base := (934184583025580780572180849390879272151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-36952582791787858543242073600500000000000000)
      constant := (513900181845129589050386035449869820548258195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417628463178026014719/100000000000000000000)
  centralHi := (40784029607229103/9765625000000000)
  directionLo := (84088161567497804129/20000000000000000000)
  directionHi := (210220403918744510323/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree076.table
  base := (705999901230113997010988703738142267197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (112812)
      previous := (69258)
      next := (0)
      square := (2990430703258893959002595604900000000000000)
      linear := (-165043541564827940857709820872370000000000000)
      constant := (2281225461377697561628230039957178540184896985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree076.table
  base := (282380044650685172433668888578875564307/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-37468578677840373579305266567620000000000000)
      constant := (529036941701127834958257563757470375952118075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84088161567497804129/20000000000000000000)
  centralHi := (210220403918744510323/50000000000000000000)
  directionLo := (42323446520060356179/10000000000000000000)
  directionHi := (423234465200603561791/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree077.table
  base := (950707657427126937399504708015236793543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (112812)
      previous := (69258)
      next := (0)
      square := (2990430703258893959002595604900000000000000)
      linear := (-167318614335150393516715717136490000000000000)
      constant := (2347621864418212064789196959586644154500026715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree077.table
  base := (1901326387615689993215172306146123882569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-37984574563892888615368459534740000000000000)
      constant := (544390951079085410465409835675033149010312205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42323446520060356179/10000000000000000000)
  centralHi := (423234465200603561791/100000000000000000000)
  directionLo := (213004901453136428523/50000000000000000000)
  directionHi := (426009802906272857047/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree078.table
  base := (2402541603562528987006625063788747746941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (75208)
      previous := (46172)
      next := (0)
      square := (1993620468839262639335063736600000000000000)
      linear := (-113062458070315230783814408933740000000000000)
      constant := (1609973224413221754693324419651708221482989235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree078.table
  base := (480492438063886985722236554560931800633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-38500570449945403651431652501860000000000000)
      constant := (559962208699031519807671210194694732259573425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213004901453136428523/50000000000000000000)
  centralHi := (426009802906272857047/100000000000000000000)
  directionLo := (1071917941737035391/250000000000000000)
  directionHi := (428767176694814156401/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree079.table
  base := (2915377765131538000494468067810252581963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-343737519751590597669455019329460000000000000)
      constant := (4966478744215705559892592715800220334828428815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree079.table
  base := (2915306849408717791659850867589761044049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-39016566335997918687494845468980000000000000)
      constant := (575750713431039825528215208727175204708650805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1071917941737035391/250000000000000000)
  centralHi := (428767176694814156401/100000000000000000000)
  directionLo := (43150693094021389323/10000000000000000000)
  directionHi := (431506930940213893231/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree080.table
  base := (859980750052813828247238382617781123429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-87071916323058875746866702964425000000000000)
      constant := (1276230232842249483514671079528744243510194145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree080.table
  base := (1719929837029226899360156109966301793393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-19766281111025216861779019218050000000000000)
      constant := (295878232138434040057340391128501306091452885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43150693094021389323/10000000000000000000)
  centralHi := (431506930940213893231/100000000000000000000)
  directionLo := (434229399152156739781/100000000000000000000)
  directionHi := (217114699576078369891/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree081.table
  base := (1988088300524990401898846459564154544179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (37604)
      previous := (23086)
      next := (0)
      square := (996810234419631319667531868300000000000000)
      linear := (-58806301805480068050913100730990000000000000)
      constant := (874207704249205254418107258838728609949015965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree081.table
  base := (1988060026727496408106954007254988775477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-20024279054051474379810615701610000000000000)
      constant := (303989730176945279562023384398017458780564265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (434229399152156739781/100000000000000000000)
  centralHi := (217114699576078369891/50000000000000000000)
  directionLo := (436934904449900407147/100000000000000000000)
  directionHi := (109233726112475101787/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree082.table
  base := (1131034485130542165362931331107013406427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-89346989093381328405872599228545000000000000)
      constant := (1346863654609659653491079145981564709350583135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree082.table
  base := (4524087447061662325602718494503163067371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-40564553994155463795684424370340000000000000)
      constant := (624419700881031770767025874295669070632351095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (436934904449900407147/100000000000000000000)
  centralHi := (109233726112475101787/25000000000000000000)
  directionLo := (439623760009902259229/100000000000000000000)
  directionHi := (43962376000990225923/10000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree083.table
  base := (5083806462497865530506004304415052477813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-361938101914170218941502189442420000000000000)
      constant := (5531546102966749153038140581819009757473958065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree083.table
  base := (1016752275218734022993727090061216847637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-41080549880207978831747617337460000000000000)
      constant := (641077185166447690297396432393024291724177325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439623760009902259229/100000000000000000000)
  centralHi := (43962376000990225923/10000000000000000000)
  directionLo := (221148134744476578371/50000000000000000000)
  directionHi := (442296269488953156743/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree084.table
  base := (2827590836693363758662265563666628415883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (37604)
      previous := (23086)
      next := (0)
      square := (996810234419631319667531868300000000000000)
      linear := (-61081374575802520709918996995110000000000000)
      constant := (946253445443403453565563230534022834182852805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree084.table
  base := (2827570708024722629762851215697149970201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-20798272883130246933905405152290000000000000)
      constant := (328975956298366773864421368008546381706940445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221148134744476578371/50000000000000000000)
  centralHi := (442296269488953156743/100000000000000000000)
  directionLo := (444952727424436868547/100000000000000000000)
  directionHi := (111238181856109217137/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree085.table
  base := (1559565783677694241865144250178386954409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1912500000000000000000000000000000000000000
      center := (3318)
      previous := (2037)
      next := (0)
      square := (87953844213496881147135164850000000000000)
      linear := (-5456446955815588670257731977925000000000000)
      constant := (85667328262018341465205195296111466020122885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree085.table
  base := (779778398770648997131601853306129147321/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212500000000000000000000000000000000000000
      center := (364)
      previous := (231)
      next := (0)
      square := (9772649357055209016348351650000000000000)
      linear := (-619302083122250130939323577525000000000000)
      constant := (9927115920992142031706695426537041955044570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444952727424436868547/100000000000000000000)
  centralHi := (111238181856109217137/25000000000000000000)
  directionLo := (17903736784528340541/4000000000000000000)
  directionHi := (223796709806604256763/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree086.table
  base := (854131307072313558130533088072242377341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-93897134634026233723884391756785000000000000)
      constant := (1493779761341672404956618629841881024234639410) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree086.table
  base := (6833018363676539809661626206536725025071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-42628537538365523939937196238820000000000000)
      constant := (692353094774909506267385430765493567661227595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17903736784528340541/4000000000000000000)
  centralHi := (223796709806604256763/50000000000000000000)
  directionLo := (450218623470471609819/100000000000000000000)
  directionHi := (22510931173523580491/5000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree087.table
  base := (371977164597451080237937515713403774517/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10837500000000000000000000000000000000000000
      center := (18802)
      previous := (11543)
      next := (0)
      square := (498405117209815659833765934150000000000000)
      linear := (-31678223673062486684462446629615000000000000)
      constant := (510561903232956751016649795471649026812655975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree087.table
  base := (7439514638786042153199996143042048167187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-43144533424418038976000389205940000000000000)
      constant := (709879548608747781719833318380667759601585215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (450218623470471609819/100000000000000000000)
  centralHi := (22510931173523580491/5000000000000000000)
  directionLo := (113207152092482331639/25000000000000000000)
  directionHi := (452828608369929326557/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree088.table
  base := (402887066579442963773877646051230715333/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-96172207404348686382890288020905000000000000)
      constant := (1570062424520510071755930618698489277264528325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree088.table
  base := (8057715750248202822366317892540796926609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-43660529310470554012063582173060000000000000)
      constant := (727623243745700742525638130105793451558950005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113207152092482331639/25000000000000000000)
  centralHi := (452828608369929326557/100000000000000000000)
  directionLo := (22771181798319524549/5000000000000000000)
  directionHi := (455423635966390490981/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree089.table
  base := (1085955537454554480829395918839807119419/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 32512500000000000000000000000000000000000000
      center := (56406)
      previous := (34629)
      next := (0)
      square := (1495215351629446979501297802450000000000000)
      linear := (-97309743789509912712393236152965000000000000)
      constant := (1608909904909696880793186227995120383176088190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree089.table
  base := (8687621461494955652297727400463554249393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-44176525196523069048126775140180000000000000)
      constant := (745584179843927533076573027382017835890372885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22771181798319524549/5000000000000000000)
  centralHi := (455423635966390490981/100000000000000000000)
  directionLo := (458003960501923940133/100000000000000000000)
  directionHi := (229001980250961970067/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree090.table
  base := (4664625974849792384013102857586137597827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (37604)
      previous := (23086)
      next := (0)
      square := (996810234419631319667531868300000000000000)
      linear := (-65631520116447426027930789523350000000000000)
      constant := (1098818766710232099110240631288935906486580045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree090.table
  base := (932923156123430848616414778934115759787/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-22346260541287792042094984053650000000000000)
      constant := (381881178299055612353009274560698986364461075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458003960501923940133/100000000000000000000)
  centralHi := (229001980250961970067/50000000000000000000)
  directionLo := (230284914548287575681/50000000000000000000)
  directionHi := (460569829096575151363/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree091.table
  base := (9982564061421043286581047926464189213981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-398339266239329461485596529668340000000000000)
      constant := (6752068637084109299386148692809934780727822905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree091.table
  base := (9982545860463383392877599051599162082433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-45208516968628099120253161074420000000000000)
      constant := (782157773735142658803552564212988789209115685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230284914548287575681/50000000000000000000)
  centralHi := (460569829096575151363/100000000000000000000)
  directionLo := (463121482024586051441/100000000000000000000)
  directionHi := (231560741012293025721/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree092.table
  base := (5323790218727399868431588889026182908673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (112812)
      previous := (69258)
      next := (0)
      square := (2990430703258893959002595604900000000000000)
      linear := (-201444705889987183401804161098290000000000000)
      constant := (3456553863770226377818928866971681508727292365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree092.table
  base := (10647564189844506617256043674998015426689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-45724512854680614156316354041540000000000000)
      constant := (800770431010328896792937028451604132291565605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463121482024586051441/100000000000000000000)
  centralHi := (231560741012293025721/50000000000000000000)
  directionLo := (465659152976991873297/100000000000000000000)
  directionHi := (232829576488495936649/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree093.table
  base := (11324300900803309229822335664750156986809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (75208)
      previous := (46172)
      next := (0)
      square := (1993620468839262639335063736600000000000000)
      linear := (-135813185773539757373873371574940000000000000)
      constant := (2358676623109523297378157428322815930537817015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree093.table
  base := (353883949918733409714004732961160783511/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3612500000000000000000000000000000000000000
      center := (6188)
      previous := (3927)
      next := (0)
      square := (166135039069938553277921978050000000000000)
      linear := (-11560127185183282298094886752165000000000000)
      constant := (204900082051015356649789942422834018657387160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465659152976991873297/100000000000000000000)
  centralHi := (232829576488495936649/50000000000000000000)
  directionLo := (234091534655703674417/50000000000000000000)
  directionHi := (93636613862281469767/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree094.table
  base := (1201272529247176934311044910377307801111/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (112812)
      previous := (69258)
      next := (0)
      square := (2990430703258893959002595604900000000000000)
      linear := (-205994851430632088719815953626530000000000000)
      constant := (3620417530190366651686677831623288439767242775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree094.table
  base := (12012712346482716647298609389276552584457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-46756504626785644228442739975780000000000000)
      constant := (838647465118887422365137360644872618484540365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234091534655703674417/50000000000000000000)
  centralHi := (93636613862281469767/20000000000000000000)
  directionLo := (94138690457951579883/20000000000000000000)
  directionHi := (58836681536219737427/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree095.table
  base := (2542570693880210776233205931196377767137/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-416539848401909082757643699781300000000000000)
      constant := (7407523298836459053181230711626744464308083425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree095.table
  base := (12712841913999145870691598572762455066241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-47272500512838159264505932942900000000000000)
      constant := (857911841576934459741571442993341747570718245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94138690457951579883/20000000000000000000)
  centralHi := (58836681536219737427/12500000000000000000)
  directionLo := (29574407331541210327/6250000000000000000)
  directionHi := (473190517304659365233/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree096.table
  base := (6712342651322815018856206370552808090289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (37604)
      previous := (23086)
      next := (0)
      square := (996810234419631319667531868300000000000000)
      linear := (-70181665657092331345942582051590000000000000)
      constant := (1262682430503135081235411567873754423071402815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree096.table
  base := (13424674988836473081701899440331442268631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-47788496398890674300569125910020000000000000)
      constant := (877393457417645288782937074465486934078171795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29574407331541210327/6250000000000000000)
  centralHi := (473190517304659365233/100000000000000000000)
  directionLo := (29729654630943862437/6250000000000000000)
  directionHi := (475674474095101798993/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree097.table
  base := (14148220675766919344631932725317858917209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-425640139483198893393667284837780000000000000)
      constant := (7746548911413503893089201508526010755218303045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree097.table
  base := (14148211470485887569882955673311478819843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24752)
      previous := (15708)
      next := (0)
      square := (664540156279754213111687912200000000000000)
      linear := (-48304492284943189336632318877140000000000000)
      constant := (897092312495784678012638981180827086894673135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell017.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29729654630943862437/6250000000000000000)
  centralHi := (475674474095101798993/100000000000000000000)
  directionLo := (23907276347602428773/5000000000000000000)
  directionHi := (478145526952048575461/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree098.table
  base := (14883459483416181247341596466290111271369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (225624)
      previous := (138516)
      next := (0)
      square := (5980861406517787918005191209800000000000000)
      linear := (-430190285023843798711679077366020000000000000)
      constant := (7918886282650478899299075189661214897084153845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree098.table
  base := (1488345126782797149344157800587249404413/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (12376)
      previous := (7854)
      next := (0)
      square := (332270078139877106555843956100000000000000)
      linear := (-24410244085497852186347755922130000000000000)
      constant := (458504203339842534324643002325118876946883925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell017.Kernel098
