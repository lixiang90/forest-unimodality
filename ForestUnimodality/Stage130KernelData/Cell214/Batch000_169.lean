import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell214.Parameters
import ForestUnimodality.BinomialMassData.Q6_11.Batch000_049
import ForestUnimodality.BinomialMassData.Q6_11.Batch050_099
import ForestUnimodality.BinomialMassData.Q6_11.Batch100_149
import ForestUnimodality.BinomialMassData.Q6_11.Batch150_199
import ForestUnimodality.BinomialMassData.Q97_177.Batch000_049
import ForestUnimodality.BinomialMassData.Q97_177.Batch050_099
import ForestUnimodality.BinomialMassData.Q97_177.Batch100_149
import ForestUnimodality.BinomialMassData.Q97_177.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree000.table
  base := (378278538461744275222997659/10000000000000000000000000)
  polynomial :=
    { denominator := 27500000000000000000000000000000000000000
      center := (126)
      previous := (0)
      next := (105)
      square := (1710094006430919848227301120000000000000)
      linear := (-8024200223772392503995831625000000000000)
      constant := (1040265980769796756863243562250000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree000.table
  base := (378278538461744275222997659/10000000000000000000000000)
  polynomial :=
    { denominator := 147500000000000000000000000000000000000000
      center := (679)
      previous := (0)
      next := (560)
      square := (9172322398129479185946433280000000000000)
      linear := (-43038892109324650703250369625000000000000)
      constant := (5579608442310728059539215470250000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree001.table
  base := (227235366840571795968756038957757376064053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-435149322154669422890727045260000000000000)
      constant := (27710446878254820410328538069368642503750413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree001.table
  base := (226529212990109971447757662998589425370679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-112767773383050985638587081759340000000000000)
      constant := (7152881993093866834306099863867428107438002391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49768848690497718649/100000000000000000000)
  directionHi := (995376973809954373/2000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree002.table
  base := (143127222814450260461278185725783959373843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-517233834463353575605637499020000000000000)
      constant := (17793102311989939068059089976739859084235003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree002.table
  base := (35586618264807661983005112994683756175133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-33530234981474103295867594608795000000000000)
      constant := (1145792807737243834375575509673317397210741757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768848690497718649/100000000000000000000)
  centralHi := (995376973809954373/2000000000000000000)
  directionLo := (2815351232071853011/4000000000000000000)
  directionHi := (17595945200449081319/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree003.table
  base := (1902395733934812548825462764393688135157/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-299659173386018864160273976390000000000000)
      constant := (6144358386496544641400083084950906608849925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree003.table
  base := (47229162249607923440633775125211903943289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-8637450359374546707130759728390000000000000)
      constant := (175679763315822986433635047688672637626589009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2815351232071853011/4000000000000000000)
  centralHi := (17595945200449081319/25000000000000000000)
  directionLo := (86202174566149834763/100000000000000000000)
  directionHi := (21550543641537458691/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree004.table
  base := (2086259512237698761975150661762096103593/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-170350714770180470258864601635000000000000)
      constant := (2301626753917012533740475385505709028278024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree004.table
  base := (6624728208932819310682863144396905633311/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-88413636505793634136618485893430000000000000)
      constant := (1184733162410450430964816834070013282930001595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86202174566149834763/100000000000000000000)
  centralHi := (21550543641537458691/25000000000000000000)
  directionLo := (49768848690497718649/50000000000000000000)
  directionHi := (99537697380995437299/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree005.table
  base := (24619793270408179279261741694468393002381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-381743685694703016875184430150000000000000)
      constant := (3740280563834429218194888098530675553288101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree005.table
  base := (48852035822959631696387431800320116043079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-198180439554432695818120268462700000000000000)
      constant := (1927247005160212903526954240617728915513621991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768848690497718649/50000000000000000000)
  centralHi := (99537697380995437299/100000000000000000000)
  directionLo := (111286528833854290641/100000000000000000000)
  directionHi := (55643264416927145321/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree006.table
  base := (2363657630746986284226276375649972181789/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-211392970924522546616319828515000000000000)
      constant := (1634361667913208593827784272634586535985876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree006.table
  base := (18762116650980152433160325050747133470951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-12196311449848784631277975841030000000000000)
      constant := (93712036023395165894125453998390771612380431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111286528833854290641/100000000000000000000)
  centralHi := (55643264416927145321/50000000000000000000)
  directionLo := (121908284377502166973/100000000000000000000)
  directionHi := (60954142188751083487/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree007.table
  base := (14963104462087840813062990304142907280519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-463828198003387169590094883910000000000000)
      constant := (3033042245499353820038627897061291780942799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree007.table
  base := (1187905977487567851375678969049061067849/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-240886772640123550907886861814380000000000000)
      constant := (1567777988785902208958914039752830854866033025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121908284377502166973/100000000000000000000)
  centralHi := (60954142188751083487/50000000000000000000)
  directionLo := (32918999168264892921/25000000000000000000)
  directionHi := (26335199334611914337/20000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree008.table
  base := (12075815552199828514826206864883931945059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-504870454157729245947550110790000000000000)
      constant := (2947870828901390627098607554010955765352139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree008.table
  base := (4793742309513709550100672533390419592283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-262239939182968978452770158490220000000000000)
      constant := (1526158497729095485470050301572622277033170535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32918999168264892921/25000000000000000000)
  centralHi := (26335199334611914337/20000000000000000000)
  directionLo := (2815351232071853011/2000000000000000000)
  directionHi := (140767561603592650551/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree009.table
  base := (3941428782648882910796766972887223971727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-1091825420624142644610010675340000000000000)
      constant := (5931113161020160860960892764476770502894835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree009.table
  base := (3911255398661009964668235650805553558199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-31510345080646045110850383907340000000000000)
      constant := (170831750832067580460083557615850659680453595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2815351232071853011/2000000000000000000)
  centralHi := (140767561603592650551/100000000000000000000)
  directionLo := (37326636517873288987/25000000000000000000)
  directionHi := (149306546071493155949/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree010.table
  base := (16142461004393030992240064212007881992939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-1173909932932826797324921129100000000000000)
      constant := (6117714352746498752335787007652953721145619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree010.table
  base := (16014811339146899261490934532351807559763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-304946272268659833542536751841900000000000000)
      constant := (1587801619742436681220744744511049779039815027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37326636517873288987/25000000000000000000)
  centralHi := (149306546071493155949/100000000000000000000)
  directionLo := (78691459193130617731/50000000000000000000)
  directionHi := (157382918386261235463/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree011.table
  base := (13191755989742745110230964157594543223447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (504)
      previous := (0)
      next := (420)
      square := (6840376025723679392909204480000000000000)
      linear := (-114181313203773722730893780260000000000000)
      constant := (583943658183760074453171926013539975457917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree011.table
  base := (654083332192170606082164622050990473189/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-81574859702876315271855012129435000000000000)
      constant := (417219396784784544862522549009682402672690905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78691459193130617731/50000000000000000000)
  centralHi := (157382918386261235463/100000000000000000000)
  directionLo := (82532298677175806213/50000000000000000000)
  directionHi := (165064597354351612427/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree012.table
  base := (83528033423135185533483565335265177607/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-334519739387548775688685509155000000000000)
      constant := (1707083627829436107147014515258146767694304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree012.table
  base := (331106784500567891724837872452255236337/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 8702500000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (541167021489639271970839563520000000000000)
      linear := (-9657016815398630239786204033155000000000000)
      constant := (49323787519020360724480866651030403821512776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82532298677175806213/50000000000000000000)
  centralHi := (165064597354351612427/100000000000000000000)
  directionLo := (86202174566149834763/50000000000000000000)
  directionHi := (172404349132299669527/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree013.table
  base := (1707315408705445685742434285549657841989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-1420163469858879255469652490380000000000000)
      constant := (7319826086674950685344472214877542994403345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree013.table
  base := (8451914408050309962164594773606110441443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-369005771897196116177186641869420000000000000)
      constant := (1904875047924450847967346195277085834019967747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86202174566149834763/50000000000000000000)
  centralHi := (172404349132299669527/100000000000000000000)
  directionLo := (1401907311518737053/781250000000000000)
  directionHi := (35888827174879668557/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree014.table
  base := (1331048858233034607085488588442191639557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-1502247982167563408184562944140000000000000)
      constant := (7889206128737262709208169732087525941931985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree014.table
  base := (658041745446477690267538581107967066493/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-195179469220020771861034969272630000000000000)
      constant := (1027158715445090000992270327771917501130795985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1401907311518737053/781250000000000000)
  centralHi := (35888827174879668557/20000000000000000000)
  directionLo := (37243596066807077743/20000000000000000000)
  directionHi := (46554495083508847179/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree015.table
  base := (4996673482608958455107753415181801897299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-1584332494476247560899473397900000000000000)
      constant := (8530313736350272827466951756236998029573179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree015.table
  base := (2465222897494715705362264121397295550219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-22872894721271498403719624178950000000000000)
      constant := (123466777645444584061476519206833985810312339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37243596066807077743/20000000000000000000)
  centralHi := (46554495083508847179/25000000000000000000)
  directionLo := (96376961069107236177/50000000000000000000)
  directionHi := (38550784427642894471/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree016.table
  base := (35229990669407695421049603142586852821/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-416604251696232928403595962915000000000000)
      constant := (2309641794463231351874348260226325229783525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree016.table
  base := (108262303013827779718297484768971160667/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-108266317881433099702959132974235000000000000)
      constant := (601987649523266563406553066808296779940291544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96376961069107236177/50000000000000000000)
  centralHi := (38550784427642894471/20000000000000000000)
  directionLo := (199075394761990874597/100000000000000000000)
  directionHi := (99537697380995437299/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree017.table
  base := (551266169547843885353922587169338650783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-437125379773403966582323576355000000000000)
      constant := (2502609633240735881986021354477489976744743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree017.table
  base := (538316125630255279698904178978836010349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-113604609517144456589179957143195000000000000)
      constant := (652513699017514194888441586904022953368223821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199075394761990874597/100000000000000000000)
  centralHi := (99537697380995437299/50000000000000000000)
  directionLo := (205202220016305282259/100000000000000000000)
  directionHi := (10260111000815264113/5000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree018.table
  base := (509911798997765854361798261353597165343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-915293015701150009522102379590000000000000)
      constant := (5421569574379066287372375450383785257006503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree018.table
  base := (194823201056381800425929880216068889111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-52863511623491472655733680583180000000000000)
      constant := (314221759457369346499378113532480679014976955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205202220016305282259/100000000000000000000)
  centralHi := (10260111000815264113/5000000000000000000)
  directionLo := (8446053696215559033/4000000000000000000)
  directionHi := (105575671202694487913/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree019.table
  base := (-25643181658993763531160427855091440353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-956335271855492085879557606470000000000000)
      constant := (5867211500144137126898689263369533935717287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree019.table
  base := (-91539098021949681963522472661048733833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-497124771154268681446486421924460000000000000)
      constant := (3061194526524104303025546023424822004217745943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8446053696215559033/4000000000000000000)
  centralHi := (105575671202694487913/50000000000000000000)
  directionLo := (216937381978246140177/100000000000000000000)
  directionHi := (108468690989123070089/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree020.table
  base := (-511704900512174718955921451002446804703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-997377528009834162237012833350000000000000)
      constant := (6341228795762536662596812390428703936630937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree020.table
  base := (-264696527592420078588434435801710266129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-129619484424278527247842429650075000000000000)
      constant := (827294565709091078522481042890268219072444559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216937381978246140177/100000000000000000000)
  centralHi := (108468690989123070089/50000000000000000000)
  directionLo := (111286528833854290641/50000000000000000000)
  directionHi := (222573057667708581283/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree021.table
  base := (-1909010441318154098410427762305802442729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-2076839568328352477188936120460000000000000)
      constant := (13685734811598983179908649227440997904429791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree021.table
  base := (-388007542065930344772292007126621564749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-59981233804439948504028112808460000000000000)
      constant := (396839796360692858294380129032341151665543655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111286528833854290641/50000000000000000000)
  centralHi := (222573057667708581283/100000000000000000000)
  directionLo := (45613903275001926181/20000000000000000000)
  directionHi := (114034758187504815453/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree022.table
  base := (-679601105424181017403845108396272032873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27500000000000000000000000000000000000000
      center := (126)
      previous := (0)
      next := (105)
      square := (1710094006430919848227301120000000000000)
      linear := (-49066456378114468861451058505000000000000)
      constant := (335068327451655177001239044587641007638397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree022.table
  base := (-686390904444672235166027735790542680489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-140296067695701241020284077987995000000000000)
      constant := (962003124924924370833402137880188088362960119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45613903275001926181/20000000000000000000)
  centralHi := (114034758187504815453/50000000000000000000)
  directionLo := (46687318449235630803/20000000000000000000)
  directionHi := (7294893507693067313/3125000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree023.table
  base := (-865040535817303563871055604375443624453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-560252148236430195654689256995000000000000)
      constant := (3963308840453099851563092720600571321441187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree023.table
  base := (-1741945418742712688104817930911515336137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-291268718662825195813009804313910000000000000)
      constant := (2069137058832176536997616830468963136034163927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46687318449235630803/20000000000000000000)
  centralHi := (7294893507693067313/3125000000000000000)
  directionLo := (119341506714434960603/50000000000000000000)
  directionHi := (238683013428869921207/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree024.table
  base := (-4141420827927273829290000916272546340497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-2323093105254404935333667481740000000000000)
      constant := (17015558069568808484536169277611021892799863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree024.table
  base := (-1040528906482048925504052980195402711941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8702500000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (541167021489639271970839563520000000000000)
      linear := (-16774738996347106088080636258435000000000000)
      constant := (123392241736694243047508431062859803159733379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119341506714434960603/50000000000000000000)
  centralHi := (238683013428869921207/100000000000000000000)
  directionLo := (121908284377502166973/50000000000000000000)
  directionHi := (243816568755004333947/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree025.table
  base := (-4768133381906552838208256590912784188503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-2405177617563089088048577935500000000000000)
      constant := (18229254229487541367197672727499553113191137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree025.table
  base := (-4786152236611046234541525333185721098521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-625243770411341246715786201979500000000000000)
      constant := (4759366966621588243430515272124124543704435591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121908284377502166973/50000000000000000000)
  centralHi := (243816568755004333947/100000000000000000000)
  directionLo := (248844243452488593247/100000000000000000000)
  directionHi := (7776382607890268539/3125000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree026.table
  base := (-2672634922581773481065935497461295259801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-1243631064935886620381744194630000000000000)
      constant := (9746861233366931038484921282047183273564079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree026.table
  base := (-5360934433262829382943789490580744926023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-646596936954186674260669498655340000000000000)
      constant := (5089858340082278338029351255177715842212625433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248844243452488593247/100000000000000000000)
  centralHi := (7776382607890268539/3125000000000000000)
  directionLo := (253772330641894583587/100000000000000000000)
  directionHi := (63443082660473645897/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree027.table
  base := (-5876982307475035438330628065518345019651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-2569346642180457393478398843020000000000000)
      constant := (20808460378444780326143034930992280252622229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree027.table
  base := (-58905805068561164099966475945822311969/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8702500000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (541167021489639271970839563520000000000000)
      linear := (-18554169541584225050154244314755000000000000)
      constant := (150929605582366204122649333321119813300897775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253772330641894583587/100000000000000000000)
  centralHi := (63443082660473645897/25000000000000000000)
  directionLo := (25860652369844950429/10000000000000000000)
  directionHi := (258606523698449504291/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree028.table
  base := (-636674093429763072415446318788222681929/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-1325715577244570773096654648390000000000000)
      constant := (11086524037300023003688953823293125277432955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree028.table
  base := (-1275705874850435551092855633345753854033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-689303270039877529350436092007020000000000000)
      constant := (5790081611443956532981217556370634387535000715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25860652369844950429/10000000000000000000)
  centralHi := (258606523698449504291/100000000000000000000)
  directionLo := (263351993346119143369/100000000000000000000)
  directionHi := (26335199334611914337/10000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree029.table
  base := (-1704361679464993820681306318816983647277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-683378916699456424727054937635000000000000)
      constant := (5896783633784998345659179248093144978679483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree029.table
  base := (-6827653350846965063233990862941959831773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-710656436582722956895319388682860000000000000)
      constant := (6159615784749558122675530401398311340430383683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263351993346119143369/100000000000000000000)
  centralHi := (26335199334611914337/10000000000000000000)
  directionLo := (67003363114917615141/25000000000000000000)
  directionHi := (53602690491934092113/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree030.table
  base := (-1446305047162687492625354387034046702743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-2815600179106509851623130204300000000000000)
      constant := (25050426265168806881680316197844401744840485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree030.table
  base := (-1810087969353008748493773278087090110487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8702500000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (541167021489639271970839563520000000000000)
      linear := (-20333600086821344012227852371075000000000000)
      constant := (181722031911168222746561272283228839325394753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67003363114917615141/25000000000000000000)
  centralHi := (53602690491934092113/20000000000000000000)
  directionLo := (54519042177694095851/20000000000000000000)
  directionHi := (34074401361058809907/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree031.table
  base := (-1522200955616044337030573935900071422431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-2897684691415194004338040658060000000000000)
      constant := (26562677841605899769713659515060456789429245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree031.table
  base := (-1523725913801229691334815913312752802727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-753362769668413811985085982034540000000000000)
      constant := (6937150901016274301065605867823943837216829085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54519042177694095851/20000000000000000000)
  centralHi := (34074401361058809907/12500000000000000000)
  directionLo := (27710122211803280139/10000000000000000000)
  directionHi := (277101222118032801391/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree032.table
  base := (-397879076737308398390953154813732626893/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-744942300930969539263237777955000000000000)
      constant := (7030921006362721351108966512217691760729735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree032.table
  base := (-497760080580443719799922825118732271703/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-193678984052814809882492319677595000000000000)
      constant := (1836259142397169484741672355722140946639266852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27710122211803280139/10000000000000000000)
  centralHi := (277101222118032801391/100000000000000000000)
  directionLo := (2815351232071853011/1000000000000000000)
  directionHi := (281535123207185301101/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree033.table
  base := (-1034084254287843118395850242861576648687/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27500000000000000000000000000000000000000
      center := (126)
      previous := (0)
      next := (105)
      square := (1710094006430919848227301120000000000000)
      linear := (-69587584455285507040178671945000000000000)
      constant := (675756208517188547292861826787045313728886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree033.table
  base := (-8278346450201632058158455176057879692481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-88452122528233851897205841709580000000000000)
      constant := (862845145815820821493732749567162520790473639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2815351232071853011/1000000000000000000)
  centralHi := (281535123207185301101/100000000000000000000)
  directionLo := (35737533643579534583/12500000000000000000)
  directionHi := (57180053829727255333/20000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree034.table
  base := (-8557468629724998471118839922951044820319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-3143938228341246462482772019340000000000000)
      constant := (31391301740812151251465169306202923576741401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree034.table
  base := (-8562354344029164624629464931324758588431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-817422269296950094619735872062060000000000000)
      constant := (8198823496519580760935220750980246638183045201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35737533643579534583/12500000000000000000)
  centralHi := (57180053829727255333/20000000000000000000)
  directionLo := (145099881288063361797/50000000000000000000)
  directionHi := (58039952515225344719/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree035.table
  base := (-275404922431841494409194115418318718763/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-806505685162482653799420618275000000000000)
      constant := (8274412416951231250780477409525067480237416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree035.table
  base := (-176343240020596947980397318998354077271/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-419387717919897761082309584368950000000000000)
      constant := (4322328756369618898182186683024764127829421025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145099881288063361797/50000000000000000000)
  centralHi := (58039952515225344719/20000000000000000000)
  directionLo := (294436479565997353259/100000000000000000000)
  directionHi := (14721823978299867663/5000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree036.table
  base := (-9039970524633663136129501033521935411941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-3308107252958614767912592926860000000000000)
      constant := (34852216546782672589032714737023845815155139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree036.table
  base := (-4521792905797841812233996935814763840313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-47784922354591163872750136967430000000000000)
      constant := (505726821350375968340376204114068807071870447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294436479565997353259/100000000000000000000)
  centralHi := (14721823978299867663/5000000000000000000)
  directionLo := (37326636517873288987/12500000000000000000)
  directionHi := (298613092142986311897/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree037.table
  base := (-9239201682894882879951518107363352548861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-3390191765267298920627503380620000000000000)
      constant := (36654918399785586915086640573129034341587819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree037.table
  base := (-9242307943412888633231865960374529528087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-881481768925486377254385762089580000000000000)
      constant := (9574077939590728222078104252130206364414562377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37326636517873288987/12500000000000000000)
  centralHi := (298613092142986311897/100000000000000000000)
  directionLo := (302732087990641140629/100000000000000000000)
  directionHi := (30273208799064114063/10000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree038.table
  base := (-75289851654429813658559709390597294379/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-3472276277575983073342413834380000000000000)
      constant := (38505684990645330083057763354587215922517625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree038.table
  base := (-470694920610873762306486964168177421497/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-225708733867082951199817264691355000000000000)
      constant := (2514406280142031656638738981155445847809602435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302732087990641140629/100000000000000000000)
  centralHi := (30273208799064114063/10000000000000000000)
  directionLo := (38349473472418542941/12500000000000000000)
  directionHi := (306795787779348343529/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree039.table
  base := (-4778272664061372874255823913954417751869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-1777180394942333613028662144070000000000000)
      constant := (20202228788034316703091294529951515452023851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree039.table
  base := (-9558833522237590657836021950293740178501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-102687566890130803593794706160140000000000000)
      constant := (1172634378344866557788374684428807490438638019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38349473472418542941/12500000000000000000)
  centralHi := (306795787779348343529/100000000000000000000)
  directionLo := (155403180227375497307/50000000000000000000)
  directionHi := (62161272090950198923/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree040.table
  base := (-1935109867973695494584966571147273651543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-3636445302193351378772234741900000000000000)
      constant := (42351187024850495850663927952455899440816485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree040.table
  base := (-9677511273977048032375679296700633646093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-945541268554022659889035652117100000000000000)
      constant := (11062318324239961440083614818845665848501552403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155403180227375497307/50000000000000000000)
  centralHi := (62161272090950198923/20000000000000000000)
  directionLo := (12590633470900898837/4000000000000000000)
  directionHi := (157382918386261235463/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree041.table
  base := (-48842915479674143175830638387194370683/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-929632453625508882871786298915000000000000)
      constant := (11086458061229938674798595088227474057367850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree041.table
  base := (-9770264238359164857163158232697333358077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-966894435096868087433918948792940000000000000)
      constant := (11583441458862157272956476694334045243224805667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12590633470900898837/4000000000000000000)
  centralHi := (157382918386261235463/50000000000000000000)
  directionLo := (318676121319254034661/100000000000000000000)
  directionHi := (159338060659627017331/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree042.table
  base := (-9835930633205341562473988299559230400033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-3800614326810719684202055649420000000000000)
      constant := (46388358867813501330178093084473333121596007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree042.table
  base := (-9837370314007386206653622617624511883313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-109805289071079279442089138385420000000000000)
      constant := (1346341122520490289775150217530569074134187447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318676121319254034661/100000000000000000000)
  centralHi := (159338060659627017331/50000000000000000000)
  directionLo := (322539003221411305249/100000000000000000000)
  directionHi := (1290156012885645221/400000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree043.table
  base := (-9877829514429680592324689835692356750359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-3882698839119403836916966103180000000000000)
      constant := (48478738148439026358780436858401224833206561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree043.table
  base := (-4939530857905806377396798058447592620973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-504800384091279471261842771072310000000000000)
      constant := (6331598490323220873464584984627585370777536883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322539003221411305249/100000000000000000000)
  centralHi := (1290156012885645221/400000000000000000)
  directionLo := (20397260357076682361/6250000000000000000)
  directionHi := (326356165713226917777/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree044.table
  base := (-4947239216542870670760281971544109282279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55000000000000000000000000000000000000000
      center := (252)
      previous := (0)
      next := (210)
      square := (3420188012861839696454602240000000000000)
      linear := (-180217425064913090437812570770000000000000)
      constant := (2300770274767522927971287706553014797894931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree044.table
  base := (-9895532485634342798354533854133830967667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1030953934725404370068568838820460000000000000)
      constant := (13221816013610734480675377811206161209613960557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20397260357076682361/6250000000000000000)
  centralHi := (326356165713226917777/100000000000000000000)
  directionLo := (82532298677175806213/25000000000000000000)
  directionHi := (330129194708703224853/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree045.table
  base := (-9886043573760468343093130259187748848083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-4046867863736772142346787010700000000000000)
      constant := (52802962448817915211444957265638282389381957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree045.table
  base := (-1977388953632425957579411042704460400947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-116923011252027755290383570610700000000000000)
      constant := (1532546902416267308462484648771228866721517465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82532298677175806213/25000000000000000000)
  centralHi := (330129194708703224853/100000000000000000000)
  directionLo := (333859586501562871923/100000000000000000000)
  directionHi := (83464896625390717981/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree046.table
  base := (-9852663931713457097083650067676728304271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-4128952376045456295061697464460000000000000)
      constant := (55036770541809847691505327407491115875183209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree046.table
  base := (-9853434054940002571378995891468540747963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1073660267811095225158335432172140000000000000)
      constant := (14376511060238841424612451017927102086907067173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333859586501562871923/100000000000000000000)
  centralHi := (83464896625390717981/25000000000000000000)
  directionLo := (337548754699187415447/100000000000000000000)
  directionHi := (42193594337398426931/12500000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree047.table
  base := (-9794455761950845055458218468334191135979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-4211036888354140447776607918220000000000000)
      constant := (57318356257005559223861542462651562872546541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree047.table
  base := (-9795113566237133894381479867032707580997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1095013434353940652703218728847980000000000000)
      constant := (14972579282010228513079334315024312304194944987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (337548754699187415447/100000000000000000000)
  centralHi := (42193594337398426931/12500000000000000000)
  directionLo := (4264975456020927069/1250000000000000000)
  directionHi := (341198036481674165521/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree048.table
  base := (-9711516300259994604630192975491719465319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-4293121400662824600491518371980000000000000)
      constant := (59647707828874778959757586171885501944696401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree048.table
  base := (-2428019478124027217643555798641861179369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8702500000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (541167021489639271970839563520000000000000)
      linear := (-31010183358244057784669500708995000000000000)
      constant := (432808995083611424792690366554607681234616511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4264975456020927069/1250000000000000000)
  centralHi := (341198036481674165521/100000000000000000000)
  directionLo := (344808698264599339053/100000000000000000000)
  directionHi := (172404349132299669527/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree049.table
  base := (-2400981718835640191947581703964804782611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-1093801478242877188301607206435000000000000)
      constant := (15506203854161151660346844348690258621304069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree049.table
  base := (-9604406153810613218704831113083338333743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1137719767439631507792985322199660000000000000)
      constant := (16202142206364514683102363936218832093342165553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344808698264599339053/100000000000000000000)
  centralHi := (172404349132299669527/50000000000000000000)
  directionLo := (69676388166696806109/20000000000000000000)
  directionHi := (174190970416742015273/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree050.table
  base := (-9471755511686747922310932151328474284193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-4457290425280192905921339279500000000000000)
      constant := (64449670789351969539088866359689254611612647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree050.table
  base := (-1894432871280374707457988832670411773661/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1159072933982476935337868618875500000000000000)
      constant := (16835632362285093876670938704281343347714872655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69676388166696806109/20000000000000000000)
  centralHi := (174190970416742015273/50000000000000000000)
  directionLo := (2815351232071853011/800000000000000000)
  directionHi := (43989863001122703297/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree051.table
  base := (-9315059106513840717302721745652052459071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-4539374937588877058636249733260000000000000)
      constant := (66922267062433092210319656822256101652452409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree051.table
  base := (-4657703864396016470135034360790097500017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-65579227806962353493486217530630000000000000)
      constant := (971199586730219925090329743105179670602440823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2815351232071853011/800000000000000000)
  centralHi := (43989863001122703297/12500000000000000000)
  directionLo := (88855167723542000211/25000000000000000000)
  directionHi := (71084134178833600169/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree052.table
  base := (-9133885250496951767044489645865736009819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-4621459449897561211351160187020000000000000)
      constant := (69442598477416528028752014702770245942811901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree052.table
  base := (-9134182406776069067209430123465049764871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1201779267068167790427635212227180000000000000)
      constant := (18140021357552788153497446335512443455916356441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88855167723542000211/25000000000000000000)
  centralHi := (71084134178833600169/20000000000000000000)
  directionLo := (1401907311518737053/390625000000000000)
  directionHi := (358888271748796685569/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree053.table
  base := (-8928273750544517134183116981372437013609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-4703543962206245364066070640780000000000000)
      constant := (72010660217666356230805667384573935121353311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree053.table
  base := (-2232131736233206809085588869045746447403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-305783108402753304493129627225755000000000000)
      constant := (4702729385908795434327627087299560809549311413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1401907311518737053/390625000000000000)
  centralHi := (358888271748796685569/100000000000000000000)
  directionLo := (18116134376489910663/5000000000000000000)
  directionHi := (362322687529798213261/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree054.table
  base := (-2174564475850526904225114798013692392517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-1196407118628732379195245273635000000000000)
      constant := (18656612063569090687475152589860343220505443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree054.table
  base := (-347938942516905300378154540937834985199/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-138276177794873182835266867286540000000000000)
      constant := (2166031123331266786578273173858764910413057025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18116134376489910663/5000000000000000000)
  centralHi := (362322687529798213261/100000000000000000000)
  directionLo := (365724853132506500919/100000000000000000000)
  directionHi := (9143121328312662523/2500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree055.table
  base := (-8443865560848142570056353591706798001289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (504)
      previous := (0)
      next := (420)
      square := (6840376025723679392909204480000000000000)
      linear := (-442519362438510333590535595300000000000000)
      constant := (7026359928834668985827163937491225221985821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree055.table
  base := (-8444049186886619507641500677940862608101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1265838766696704073062285102254700000000000000)
      constant := (20190108213022370572634931950541290715350803771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (365724853132506500919/100000000000000000000)
  centralHi := (9143121328312662523/2500000000000000000)
  directionLo := (46136957545370268393/12500000000000000000)
  directionHi := (73819132072592429429/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree056.table
  base := (-4082560010293317227373047823452698106907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-2474898749566148911105401001030000000000000)
      constant := (40000595143679579502803857746002223529064253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree056.table
  base := (-2041319079908688100635088363973280328559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-321797983309887375151792099732635000000000000)
      constant := (5224600286941889212517193220292161100586575089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46136957545370268393/12500000000000000000)
  centralHi := (73819132072592429429/20000000000000000000)
  directionLo := (37243596066807077743/10000000000000000000)
  directionHi := (372435960668070777431/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree057.table
  base := (-3931020385679755905510809567359430945671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-2515941005720490987462856227910000000000000)
      constant := (41380069553335994940540531455609508855573809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree057.table
  base := (-12579478028433720535609972907490184439/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-145393899975821658683561299511820000000000000)
      constant := (2402128702780540201402771321912961667479900625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37243596066807077743/10000000000000000000)
  centralHi := (372435960668070777431/100000000000000000000)
  directionLo := (375746567647299234263/100000000000000000000)
  directionHi := (46968320955912404283/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree058.table
  base := (-1883661029033421875090439512689251247819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-1278491630937416531910155727395000000000000)
      constant := (21391700925615213753569976664144600599013901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree058.table
  base := (-7534757249276869525272046332819088755197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1329898266325240355696934992282220000000000000)
      constant := (22352379252365649900931265510889790768388433187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (375746567647299234263/100000000000000000000)
  centralHi := (46968320955912404283/12500000000000000000)
  directionLo := (75805651873380543101/20000000000000000000)
  directionHi := (189514129683451357753/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree059.table
  base := (-3591471846657210540788159130765999739891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-2598025518029175140177766681670000000000000)
      constant := (44210591212239358999294130109117314031473189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree059.table
  base := (-7183039901205390443501020500708035553309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5310000000000000000000000000000000000000000
      center := (24444)
      previous := (0)
      next := (20160)
      square := (330203606332661250694071598080000000000000)
      linear := (-22902566658781114970200309982340000000000000)
      constant := (391492602003714909735364351283704033121192921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75805651873380543101/20000000000000000000)
  centralHi := (189514129683451357753/50000000000000000000)
  directionLo := (95570445123833174947/25000000000000000000)
  directionHi := (382281780495332699789/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree060.table
  base := (-1701737728167921830008214160181199378563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-1319533887091758608267610954275000000000000)
      constant := (22830818473035852971849162303618074875193877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree060.table
  base := (-3403516351955311910319762152425816925573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-76255811078385067265927865868550000000000000)
      constant := (1325345043254552284112110250316405731282080387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95570445123833174947/25000000000000000000)
  centralHi := (382281780495332699789/100000000000000000000)
  directionLo := (385507844276428944709/100000000000000000000)
  directionHi := (38550784427642894471/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree061.table
  base := (-3203337659967838909655959540610018285547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-2680110030337859292892677135430000000000000)
      constant := (47136538475210791748335913796126187787448813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree061.table
  base := (-6406744835532507165088176435276974627467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1393957765953776638331584882309740000000000000)
      constant := (24626820745911988117625045867820227661896086357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385507844276428944709/100000000000000000000)
  centralHi := (38550784427642894471/10000000000000000000)
  directionLo := (15548285374208285121/4000000000000000000)
  directionHi := (194353567177603564013/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree062.table
  base := (-2991062450866902809346358445171417030117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-2721152286492201369250132362310000000000000)
      constant := (48635295316465657924330505391694258539355843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree062.table
  base := (-1196436793640994607254298582204976538459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1415310932496622065876468178985580000000000000)
      constant := (25409893179849036712053470149752781450133089945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15548285374208285121/4000000000000000000)
  centralHi := (194353567177603564013/50000000000000000000)
  directionLo := (97970076617370361619/25000000000000000000)
  directionHi := (391880306469481446477/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree063.table
  base := (-21614477893091934919053349562269842583/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-1381097271323271722803793794595000000000000)
      constant := (25078953532770546931052701872519782339037248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree063.table
  base := (-2766678257784000288562368567564231008359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-79814672168859305190075081981190000000000000)
      constant := (1455857104414453332818568804685518911859902321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97970076617370361619/25000000000000000000)
  centralHi := (391880306469481446477/100000000000000000000)
  directionLo := (197513995009589357527/50000000000000000000)
  directionHi := (79005598003835743011/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree064.table
  base := (-5060225228441871015254089977077494314871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-5606473597601771043930085632140000000000000)
      constant := (103408746768264825635184548470853623187900609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree064.table
  base := (-1265066959897407578960252602297046042563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-364504316395578230241558693084315000000000000)
      constant := (6753356169190065302989897300225515844532543773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197513995009589357527/50000000000000000000)
  centralHi := (79005598003835743011/20000000000000000000)
  directionLo := (79630157904796349839/20000000000000000000)
  directionHi := (99537697380995437299/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree065.table
  base := (-1140721561158063499965498565360312388897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-1422139527477613799161249021475000000000000)
      constant := (26637346994565917294460049039341402200943463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree065.table
  base := (-4562922423387647638103807364593972600579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1479370432125158348511118069013100000000000000)
      constant := (27833883431297743277381444096134135432396460509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79630157904796349839/20000000000000000000)
  centralHi := (99537697380995437299/25000000000000000000)
  directionLo := (50156160747357919829/12500000000000000000)
  directionHi := (401249285978863358633/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree066.table
  base := (-808258661108035519473705054944166031869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (504)
      previous := (0)
      next := (420)
      square := (6840376025723679392909204480000000000000)
      linear := (-524603874747194486305446049060000000000000)
      constant := (9976157935200171060214674982058070868247205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree066.table
  base := (-12629137548877480759322520907888004247/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 8702500000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (541167021489639271970839563520000000000000)
      linear := (-41686766629666771557111149046915000000000000)
      constant := (796300111823062497245589907632841348577295440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50156160747357919829/12500000000000000000)
  centralHi := (401249285978863358633/100000000000000000000)
  directionLo := (80864807623223918227/20000000000000000000)
  directionHi := (12635126191128737223/3125000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree067.table
  base := (-349544968917423651888573127500945054547/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-2926363567263911751037408496710000000000000)
      constant := (56486897149220211564351838283721928241999065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree067.table
  base := (-436934468907542730822025156353416346253/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-380519191302712300900221165591195000000000000)
      constant := (7378046590386036453287641061853752638576479526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80864807623223918227/20000000000000000000)
  centralHi := (12635126191128737223/3125000000000000000)
  directionLo := (20368779179083302663/5000000000000000000)
  directionHi := (407375583581666053261/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree068.table
  base := (-2925358139595675493567055232231232808967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-5934811646836507654789727447180000000000000)
      constant := (116257558679947882964639384852420020830114993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree068.table
  base := (-73134506305623682066784587837704674037/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-385857482938423657786441989760155000000000000)
      constant := (7592507589223865427989616000150545502670948270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20368779179083302663/5000000000000000000)
  centralHi := (407375583581666053261/100000000000000000000)
  directionLo := (205202220016305282259/50000000000000000000)
  directionHi := (410404440032610564519/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree069.table
  base := (-1165510477110878207319327273051149837737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-3008448079572595903752318950470000000000000)
      constant := (59794515076868386240544092306100810869633823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree069.table
  base := (-1165519855920006780762067432766638638861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-86932394349807781038369514206470000000000000)
      constant := (1735574219053896256323613616159529330898124859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205202220016305282259/50000000000000000000)
  centralHi := (410404440032610564519/100000000000000000000)
  directionLo := (206705553081223665407/50000000000000000000)
  directionHi := (82682221232489466163/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree070.table
  base := (-1712440056845496477582757262338552599717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-6098980671453875960219548354700000000000000)
      constant := (122968208487028136597396726253257035135434243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree070.table
  base := (-856227982573317051366916138520703084567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-793068132419692743117767276196150000000000000)
      constant := (16061551531139078051503839318562784893063600457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206705553081223665407/50000000000000000000)
  centralHi := (82682221232489466163/20000000000000000000)
  directionLo := (416396062659622123747/100000000000000000000)
  directionHi := (104099015664905530937/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree071.table
  base := (-267404264677258788968917128432745675861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-1545266295940640028233614702115000000000000)
      constant := (31598773371215419109318594213629637773220819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree071.table
  base := (-1069630547757151837260100461233878557511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1607489431382230913780417849068140000000000000)
      constant := (33018331666710333087822330556724423818671737881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416396062659622123747/100000000000000000000)
  centralHi := (104099015664905530937/25000000000000000000)
  directionLo := (209679886552342932629/50000000000000000000)
  directionHi := (419359773104685865259/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree072.table
  base := (-402553309585424435711191432557007151443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-6263149696071244265649369262220000000000000)
      constant := (129869684983914852710391686236980602134675397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree072.table
  base := (-402564745020012155420896720205529401727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-180982510880564037925033460638220000000000000)
      constant := (3769557968444220235848414396150084552152588313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209679886552342932629/50000000000000000000)
  centralHi := (419359773104685865259/100000000000000000000)
  directionLo := (8446053696215559033/2000000000000000000)
  directionHi := (422302684810777951651/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree073.table
  base := (36093757437030098007807279457077922899/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-1586308552094982104591069928995000000000000)
      constant := (33347995711833286233497005073858612857341558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree073.table
  base := (288740366896229485360879940228118506703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1650195764467921768870184442419820000000000000)
      constant := (34846173176425818533522273660051386724696498287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8446053696215559033/2000000000000000000)
  centralHi := (422302684810777951651/100000000000000000000)
  directionLo := (212612614805877007351/50000000000000000000)
  directionHi := (425225229611754014703/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree074.table
  base := (502146050257484156017247317637005112403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-3213659360344306285539595084870000000000000)
      constant := (68480993480203006526451336970674077618600763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree074.table
  base := (251070971667817326782479290464992136819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-417887232752691799103766934773915000000000000)
      constant := (8944696504939094630855600214989007738654402451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212612614805877007351/50000000000000000000)
  centralHi := (425225229611754014703/100000000000000000000)
  directionLo := (26757989037618117081/6250000000000000000)
  directionHi := (428127824601889873297/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree075.table
  base := (348814403713532148750430423609354090043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-6509403232997296723794100623500000000000000)
      constant := (140579697226950182281196862531283659224476015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree075.table
  base := (872032529571860675693868596058957117259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-94050116530756256886663946431750000000000000)
      constant := (2040214456796178390646795130864131229725178579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26757989037618117081/6250000000000000000)
  centralHi := (428127824601889873297/100000000000000000000)
  directionLo := (431010872830749173817/100000000000000000000)
  directionHi := (215505436415374586909/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree076.table
  base := (627022286717015946132910703620578030993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-1647871936326495219127252769315000000000000)
      constant := (36061278391571128962303461933258089941750153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree076.table
  base := (627020812834131310530612875740614530709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-428563816024114512876208583111835000000000000)
      constant := (9420348941079944433415482922787857712632582261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (431010872830749173817/100000000000000000000)
  centralHi := (215505436415374586909/50000000000000000000)
  directionLo := (216937381978246140177/50000000000000000000)
  directionHi := (86774952791298456071/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree077.table
  base := (824085731458724166780001803648197349081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27500000000000000000000000000000000000000
      center := (126)
      previous := (0)
      next := (105)
      square := (1710094006430919848227301120000000000000)
      linear := (-151672096763969659755089125705000000000000)
      constant := (3362687179788629063275364123770130170839891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree077.table
  base := (51505280194094217434883372328297756567/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-433902107659825869762429407280795000000000000)
      constant := (9662848157272944787328204903259266846647800688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216937381978246140177/50000000000000000000)
  centralHi := (86774952791298456071/20000000000000000000)
  directionLo := (218359937430312264973/50000000000000000000)
  directionHi := (436719874860624529947/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree078.table
  base := (4108832885600094476677497415727001677337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-6755656769923349181938831984780000000000000)
      constant := (151719064203341635231207774173622967202957777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree078.table
  base := (410882865697911282716012212096778177617/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-97608977621230494810811162544390000000000000)
      constant := (2201880600149589829465081081838604424181423885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218359937430312264973/50000000000000000000)
  centralHi := (436719874860624529947/100000000000000000000)
  directionLo := (219773285113464829069/50000000000000000000)
  directionHi := (439546570226929658139/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree079.table
  base := (4945558631377575197647930075654357907169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-6837741282232033334653742438540000000000000)
      constant := (155527598396441269266606807731834177306767449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree079.table
  base := (1236388762750292357122805006775247371633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-444578690931248583534871055618715000000000000)
      constant := (10157192568351259540741413141898866724905890257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219773285113464829069/50000000000000000000)
  centralHi := (439546570226929658139/100000000000000000000)
  directionLo := (442355203087106077579/100000000000000000000)
  directionHi := (22117760154355303879/5000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree080.table
  base := (1451629957806127913299731133612348427327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-1729956448635179371842163223075000000000000)
      constant := (39845959612458374700479101015167094159706567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree080.table
  base := (5806516800202777503492074680538076028497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1799667930267839761684367519150700000000000000)
      constant := (41636151031382794854479878690314577383896782513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (442355203087106077579/100000000000000000000)
  centralHi := (22117760154355303879/5000000000000000000)
  directionLo := (111286528833854290641/25000000000000000000)
  directionHi := (89029223067083432513/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree081.table
  base := (6691716205803671924625459948968165690153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-7001910306849401640083563346060000000000000)
      constant := (163287784329718518774973255638105148048508513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree081.table
  base := (3345856820123591643984718907729338249737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-101167838711704732734958378657030000000000000)
      constant := (2369777392685804491457540420351795826447334497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111286528833854290641/25000000000000000000)
  centralHi := (89029223067083432513/20000000000000000000)
  directionLo := (111979909553619866961/25000000000000000000)
  directionHi := (89583927642895893569/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree082.table
  base := (7601147519819443279785125721710329472719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-7083994819158085792798473799820000000000000)
      constant := (167239436007625560045188130781846949866198999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree082.table
  base := (475071584286179758270924767273343777859/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-460593565838382654193533528125595000000000000)
      constant := (10922074094329413636273060166750096348866178444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111979909553619866961/25000000000000000000)
  centralHi := (89583927642895893569/20000000000000000000)
  directionLo := (28167255798383929411/6250000000000000000)
  directionHi := (450676092774142870577/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree083.table
  base := (1706962714970744966551950936879521093483/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-7166079331466769945513384253580000000000000)
      constant := (171238793459546032405364931264532110261557215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree083.table
  base := (4267405868798712627738036367223464880613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-931863714948188022159508704589110000000000000)
      constant := (22366530476212491027553978860841833931244724677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28167255798383929411/6250000000000000000)
  centralHi := (450676092774142870577/100000000000000000000)
  directionLo := (113353947576315545857/25000000000000000000)
  directionHi := (453415790305262183429/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree084.table
  base := (1898542840674535649642701602394225217039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-7248163843775454098228294707340000000000000)
      constant := (175285856665208341416928020588328506256308595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree084.table
  base := (9492712648952125034171593387259022863893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-209453399604357941318211189539340000000000000)
      constant := (5087809643189499346645885212425128658589211533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113353947576315545857/25000000000000000000)
  centralHi := (453415790305262183429/100000000000000000000)
  directionLo := (456139032750019261811/100000000000000000000)
  directionHi := (114034758187504815453/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree085.table
  base := (1047484926371279827414471432054184102497/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-3665124178042069125471602580550000000000000)
      constant := (89690312803735601472192598257892781382010685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree085.table
  base := (10474847948773237324554220207900885781793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1906433762982066899408784002529900000000000000)
      constant := (46859973881965185712898054670182826850657792897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (456139032750019261811/100000000000000000000)
  centralHi := (114034758187504815453/25000000000000000000)
  directionLo := (11471152827258165369/2500000000000000000)
  directionHi := (458846113090326614761/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree086.table
  base := (2870304658971526369682391439543889153807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-1853083217098205600914528903715000000000000)
      constant := (45880775067954017869121444574204810587610647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree086.table
  base := (11481217523685902904554114264972200002307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1927786929524912326953667299205740000000000000)
      constant := (47942122228652135869794995012871834053872276003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11471152827258165369/2500000000000000000)
  centralHi := (458846113090326614761/100000000000000000000)
  directionLo := (115384328928931694869/25000000000000000000)
  directionHi := (461537315715726779477/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree087.table
  base := (6255911109035237848954442121912980945721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-3747208690350753278186513034310000000000000)
      constant := (93856640322961234994689302691811470694432241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree087.table
  base := (2502364255495619777812421589141157008479/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-216571121785306417166505621764620000000000000)
      constant := (5448525758416902013948466980861421837732576995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115384328928931694869/25000000000000000000)
  centralHi := (461537315715726779477/100000000000000000000)
  directionLo := (232106458386047561819/50000000000000000000)
  directionHi := (464212916772095123639/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree088.table
  base := (13566659923673043588402842396122013518491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (504)
      previous := (0)
      next := (420)
      square := (6840376025723679392909204480000000000000)
      linear := (-688772899364562791735266956580000000000000)
      constant := (17450106065392060161502438060277342148703401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree088.table
  base := (13566659128315163471705398934992234586553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-1970493262610603182043433892557420000000000000)
      constant := (50143802670701334360389824591095651717362118937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232106458386047561819/50000000000000000000)
  centralHi := (464212916772095123639/100000000000000000000)
  directionLo := (46687318449235630803/10000000000000000000)
  directionHi := (466873184492356308031/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree089.table
  base := (14645731678872953214491834747189100544117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-7658586405318874861802846976140000000000000)
      constant := (196236758483054323269708345873489881165838157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree089.table
  base := (7322865503205538788133541598166434015951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-995923214576724304794158594616630000000000000)
      constant := (25631667380656729191358530458170466211285728879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46687318449235630803/10000000000000000000)
  centralHi := (466873184492356308031/100000000000000000000)
  directionLo := (117379594877583872987/25000000000000000000)
  directionHi := (469518379510335491949/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree090.table
  base := (3937259355141265951918871557580616684233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-1935167729406889753629439357475000000000000)
      constant := (50142513982377933108983660407967254618792193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree090.table
  base := (15749036852081456489788904108728510671721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-223688843966254893014800053989900000000000000)
      constant := (5821703121746515344871738064645483945648260801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117379594877583872987/25000000000000000000)
  centralHi := (469518379510335491949/100000000000000000000)
  directionLo := (118037188789695926597/25000000000000000000)
  directionHi := (472148755158783706389/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree091.table
  base := (16876577094639044695859883163520631356873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-7822755429936243167232667883660000000000000)
      constant := (204951059052137539263882342382665996394181633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree091.table
  base := (8438288307057770432548188590023157938757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1017276381119569732339041891292470000000000000)
      constant := (26769891336156245822093970081423445515063318053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118037188789695926597/25000000000000000000)
  centralHi := (472148755158783706389/100000000000000000000)
  directionLo := (94952911550508389891/20000000000000000000)
  directionHi := (29672784859533871841/6250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree092.table
  base := (1126771915908688783147946304778844530869/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-1976209985561231829986894584355000000000000)
      constant := (52344941961324620709090356020192960752940596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree092.table
  base := (1802835024841478467264627182168985281209/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1027952964390992446111483539630390000000000000)
      constant := (27348349244856727827592196894171700699374983805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94952911550508389891/20000000000000000000)
  centralHi := (29672784859533871841/6250000000000000000)
  directionLo := (477366026857739842413/100000000000000000000)
  directionHi := (238683013428869921207/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree093.table
  base := (9602179030028949888526695341842889812391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-3993462227276805736331244395590000000000000)
      constant := (106928091152064752538870239307622989667299311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree093.table
  base := (19204357716854251191950431908523526977017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-230806566147203368863094486215180000000000000)
      constant := (6207341727414123777146536668339390397406996177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477366026857739842413/100000000000000000000)
  centralHi := (238683013428869921207/50000000000000000000)
  directionLo := (119988348886965389043/25000000000000000000)
  directionHi := (479953395547861556173/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree094.table
  base := (20404599276328023215125858110496194857273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-8069008966862295625377399244940000000000000)
      constant := (218380302424411619222303580274650039577730033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree094.table
  base := (20404598986330225581740120446471425426303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-2098612261867675747312733672612460000000000000)
      constant := (57047913842316360379329140581692823287180646687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119988348886965389043/25000000000000000000)
  centralHi := (479953395547861556173/100000000000000000000)
  directionLo := (60315861330931708427/12500000000000000000)
  directionHi := (482526890647453667417/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree095.table
  base := (10814537136488022567005488594417462056667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-4075546739585489889046154849350000000000000)
      constant := (111476064101234825219535663788424512908856707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree095.table
  base := (5407268506990866691928181025843623924367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-529991357102630293714404242322075000000000000)
      constant := (14560553343894109266649624728793779893926493743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60315861330931708427/12500000000000000000)
  centralHi := (482526890647453667417/100000000000000000000)
  directionLo := (60635841620524521619/12500000000000000000)
  directionHi := (485086732964196172953/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree096.table
  base := (2287778302341520895371999600059611632073/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-4116588995739831965403610076230000000000000)
      constant := (113785829817543300590932540769876065037404165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree096.table
  base := (2859722852054068359070199922268777474907/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8702500000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (541167021489639271970839563520000000000000)
      linear := (-59481072082037961177847229610115000000000000)
      constant := (1651360392936501362282187921701555228780302534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60635841620524521619/12500000000000000000)
  centralHi := (485086732964196172953/100000000000000000000)
  directionLo := (121908284377502166973/25000000000000000000)
  directionHi := (487633137510008667893/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree097.table
  base := (24150725504252569158110651728217217278489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-8315262503788348083522130606220000000000000)
      constant := (232238896719431925043231628362434283290697169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree097.table
  base := (24150725329415925736775150045515548835741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-2162671761496212029947383562639980000000000000)
      constant := (60668196152029884774352600581793536629474929789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121908284377502166973/25000000000000000000)
  centralHi := (487633137510008667893/100000000000000000000)
  directionLo := (490166313711818306331/100000000000000000000)
  directionHi := (122541578427954576583/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree098.table
  base := (25447901694792383265649767444089379477961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-8397347016097032236237041059980000000000000)
      constant := (236953839453001437182905453636654814916833281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree098.table
  base := (25447901547124917066942601726631093614113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-2184024928039057457492266859315820000000000000)
      constant := (61899879393903984510293738966273105531836546177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490166313711818306331/100000000000000000000)
  centralHi := (122541578427954576583/25000000000000000000)
  directionLo := (19707458624502971077/4000000000000000000)
  directionHi := (246343232806287138463/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree099.table
  base := (13384655788309984306409697120219019450091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55000000000000000000000000000000000000000
      center := (252)
      previous := (0)
      next := (210)
      square := (3420188012861839696454602240000000000000)
      linear := (-385428705836623472225088705170000000000000)
      constant := (10987113083343952772663676615662409213951001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree099.table
  base := (26769311451912634896276689460570395281011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-245042010509100320559683350665740000000000000)
      constant := (7016002652309276551058744678970425545973199291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19707458624502971077/4000000000000000000)
  centralHi := (246343232806287138463/50000000000000000000)
  directionLo := (495193792063054837279/100000000000000000000)
  directionHi := (3094961200394092733/625000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree100.table
  base := (28114955133252887300393160969809764871931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-8561516040714400541666861967500000000000000)
      constant := (246526841859134121504511533177346981549503651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree100.table
  base := (5622991005589291837047856573769064609697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-2226731261124748312582033452667500000000000000)
      constant := (64400629582172377968838799928548055125785986565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495193792063054837279/100000000000000000000)
  centralHi := (3094961200394092733/625000000000000000)
  directionLo := (248844243452488593247/50000000000000000000)
  directionHi := (99537697380995437299/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree101.table
  base := (29484832349848470974401638729709817464881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-8643600553023084694381772421260000000000000)
      constant := (251384901527906955829807095637774887913250601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree101.table
  base := (29484832260933606772123728167595915109863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-2248084427667593740126916749343340000000000000)
      constant := (65669696527622872934550924663321232424476897927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248844243452488593247/50000000000000000000)
  centralHi := (99537697380995437299/20000000000000000000)
  directionLo := (500170739145887366577/100000000000000000000)
  directionHi := (250085369572943683289/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree102.table
  base := (30878943212958493948932066462216192754509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-8725685065331768847096682875020000000000000)
      constant := (256290666838258228666492128837848159323295589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree102.table
  base := (6175788627578220943874990240521627130957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-252159732690048796407977782891020000000000000)
      constant := (7439024967414247810833823710763998920214306585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (500170739145887366577/100000000000000000000)
  centralHi := (250085369572943683289/50000000000000000000)
  directionLo := (125660183281569186513/25000000000000000000)
  directionHi := (502640733126276746053/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree103.table
  base := (32297287710323306041211472529067079435151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-8807769577640452999811593328780000000000000)
      constant := (261244137788704522342451103209337116611653271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree103.table
  base := (16148643823476446360045446082856556815519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1145395380376642297608341671347510000000000000)
      constant := (34122607059558349127172165748741103068473394751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125660183281569186513/25000000000000000000)
  centralHi := (502640733126276746053/100000000000000000000)
  directionLo := (252549324339671624617/50000000000000000000)
  directionHi := (101019729735868649847/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree104.table
  base := (2108741614418687092712587467695145653437/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-2222463522487284288131625945635000000000000)
      constant := (66561328594471330822943891350284450496263508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree104.table
  base := (8434966444301993965692408208107155466177/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-578035981824032505690391659842715000000000000)
      constant := (17387916191111611561372058842271269073599859233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252549324339671624617/50000000000000000000)
  centralHi := (101019729735868649847/20000000000000000000)
  directionLo := (253772330641894583587/50000000000000000000)
  directionHi := (20301786451351566687/4000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree105.table
  base := (17603338781856093815725480186085129382719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-4485969301128910652620707118150000000000000)
      constant := (135647098302272726954267679046016300655308999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree105.table
  base := (35206677518564547332190437161540022476813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-259277454870997272256272215116300000000000000)
      constant := (7874508515822367561691341619138820818241786053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253772330641894583587/50000000000000000000)
  centralHi := (20301786451351566687/4000000000000000000)
  directionLo := (509978942210022953083/100000000000000000000)
  directionHi := (127494735552505738271/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree106.table
  base := (36697722899738020557130539552063114410373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-9054023114566505457956324690060000000000000)
      constant := (276390784467520305173414697789079636843655133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree106.table
  base := (18348861430817917415149360951602370271989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1177425130190910438925666616361270000000000000)
      constant := (36100974876343602747110048534170410658251143381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509978942210022953083/100000000000000000000)
  centralHi := (127494735552505738271/25000000000000000000)
  directionLo := (256200829330054856551/50000000000000000000)
  directionHi := (512401658660109713103/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree107.table
  base := (29853907679529267286618968907618066017/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-2284026906718797402667808785955000000000000)
      constant := (70383769491430853610062968454232971516178240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree107.table
  base := (38213001797644121605989996036037516794367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-2376203426924666305396216529398380000000000000)
      constant := (73545784095029141474386950258150399363650723743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256200829330054856551/50000000000000000000)
  centralHi := (512401658660109713103/100000000000000000000)
  directionLo := (514812973901794013277/100000000000000000000)
  directionHi := (257406486950897006639/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree108.table
  base := (39752514345470888377111011875576729493613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-9218192139183873763386145597580000000000000)
      constant := (286727077098136007209455500551664784268727173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree108.table
  base := (9938128579584993881277935043046788265379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8702500000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (541167021489639271970839563520000000000000)
      linear := (-66598794262986437026141661835395000000000000)
      constant := (2080613324143574153788660273938225869951784299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514812973901794013277/100000000000000000000)
  centralHi := (257406486950897006639/50000000000000000000)
  directionLo := (25860652369844950429/5000000000000000000)
  directionHi := (517213047396899008581/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree109.table
  base := (10329065109706311393955303971574433064811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-2325069162873139479025264012835000000000000)
      constant := (72991695465949545994862622558030506400842131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree109.table
  base := (32278328449948598769326521801577064283/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-604727440002589290121495780687515000000000000)
      constant := (19067709118715440535405061756133969511015074240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25860652369844950429/5000000000000000000)
  centralHi := (517213047396899008581/100000000000000000000)
  directionLo := (64950254365548455487/12500000000000000000)
  directionHi := (519602034924387643897/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree110.table
  base := (21452120051176302389017776536673525270383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55000000000000000000000000000000000000000
      center := (252)
      previous := (0)
      next := (210)
      square := (3420188012861839696454602240000000000000)
      linear := (-426470961990965548582543932050000000000000)
      constant := (13511554193718249333995263400903408777974213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree110.table
  base := (10726060020760119703874194735347263641809/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-610065731638300647007716604856475000000000000)
      constant := (19413013627969253196381462840447944422634234161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64950254365548455487/12500000000000000000)
  centralHi := (519602034924387643897/100000000000000000000)
  directionLo := (652475110872943343/125000000000000000)
  directionHi := (521980088698354674401/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree111.table
  base := (44516453328918261709374341509003471273999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-9464445676109926221530876958860000000000000)
      constant := (302589308291282612097591472801669420024153879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree111.table
  base := (890329066252536939439089394572425081441/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-136756449616447111976430539783430000000000000)
      constant := (4391429654444117646693137138627555292712403025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (652475110872943343/125000000000000000)
  centralHi := (521980088698354674401/100000000000000000000)
  directionLo := (262173678740601203477/50000000000000000000)
  directionHi := (104869471496240481391/20000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree112.table
  base := (46152900111716837962837139567531316305159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-9546530188418610374245787412620000000000000)
      constant := (307972129951418113441290470740791289272924239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree112.table
  base := (11538225024493690892864440333481278543113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-620742314909723360780158253194395000000000000)
      constant := (20112968569750647834350173618977954975477187177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262173678740601203477/50000000000000000000)
  centralHi := (104869471496240481391/20000000000000000000)
  directionLo := (263351993346119143369/50000000000000000000)
  directionHi := (526703986692238286739/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree113.table
  base := (23906790222117545701310472023081088353377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-4814307350363647263480348933190000000000000)
      constant := (156701328620709943540280312624852811690758617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree113.table
  base := (23906790216322175243851607403219338362457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1252161213090869435332758154726710000000000000)
      constant := (40935238004350339467239784432373848651557415353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263351993346119143369/50000000000000000000)
  centralHi := (526703986692238286739/100000000000000000000)
  directionLo := (132262529627979665831/25000000000000000000)
  directionHi := (21162004740476746533/4000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree114.table
  base := (24749247160110177195352660204173058752513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-4855349606517989339837804160070000000000000)
      constant := (159440445080265680115600731874744940109054073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree114.table
  base := (24749247155222459394256206270126805280401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-140315310706921349900577755896070000000000000)
      constant := (4627863276049690685453159667590451409181075881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132262529627979665831/25000000000000000000)
  centralHi := (21162004740476746533/4000000000000000000)
  directionLo := (3321161824887188711/625000000000000000)
  directionHi := (531385891981950193761/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree115.table
  base := (12801910433413423681334837723629740416541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-2448195931336165708097629693475000000000000)
      constant := (81101707177006060524200281297809198590401461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree115.table
  base := (5120764172540989083848351259914217083589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1273514379633714862877641451402550000000000000)
      constant := (42372531579698462318846552812766512535058798905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3321161824887188711/625000000000000000)
  centralHi := (531385891981950193761/100000000000000000000)
  directionLo := (8339241298460129827/1562500000000000000)
  directionHi := (533711443101448308929/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree116.table
  base := (1654406958710220051275578188612067312359/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-2468717059413336746276357306915000000000000)
      constant := (82495118220798939028677340256296481158363512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree116.table
  base := (52941022671775416023104087795737083378423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-2568381925810275153300166199480940000000000000)
      constant := (86201048580027580157186203860109367085162614167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8339241298460129827/1562500000000000000)
  centralHi := (533711443101448308929/100000000000000000000)
  directionLo := (67003363114917615141/12500000000000000000)
  directionHi := (536026904919340921129/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree117.table
  base := (6837329643727955322299549086740761275943/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-2489238187490507784455084920355000000000000)
      constant := (83900455671341568806329464783421264228778206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree117.table
  base := (2187945485758483498706914143848906608319/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-287748343594791175649449944017420000000000000)
      constant := (9741055025623511295406516908577471097588960975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67003363114917615141/12500000000000000000)
  centralHi := (536026904919340921129/100000000000000000000)
  directionLo := (4205721934556211159/781250000000000000)
  directionHi := (538332407623195028353/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree118.table
  base := (14120121285375329910244149265745311480893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-2509759315567678822633812533795000000000000)
      constant := (85317719528469323975769487998535182689188053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree118.table
  base := (28240242568279631981138866673022013896099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2655000000000000000000000000000000000000000
      center := (12222)
      previous := (0)
      next := (10080)
      square := (165101803166330625347035799040000000000000)
      linear := (-22127866600813271257541803329090000000000000)
      constant := (755511890771012535285128094299034689378828569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4205721934556211159/781250000000000000)
  centralHi := (538332407623195028353/100000000000000000000)
  directionLo := (135157019656158505323/25000000000000000000)
  directionHi := (540628078624634021293/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree119.table
  base := (58286566648478080986490136064437461074221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-10121121774579399443250160588940000000000000)
      constant := (346987639168089697135099293138076932789980741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree119.table
  base := (58286566644311582248529629706819087022807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-2632441425438811435934816089508460000000000000)
      constant := (90643772220966567396623520679861755177337520503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135157019656158505323/25000000000000000000)
  centralHi := (540628078624634021293/100000000000000000000)
  directionLo := (135728510660376068619/25000000000000000000)
  directionHi := (542914042641504274477/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree120.table
  base := (60116881665619714654247485384642291206949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-10203206286888083595965071042700000000000000)
      constant := (352752105847382239274138450123541717236040829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree120.table
  base := (58707892248151672350004106668665633371/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 8702500000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (541167021489639271970839563520000000000000)
      linear := (-73716516443934912874436094060675000000000000)
      constant := (2559711182233686693706548510193288017859699456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135728510660376068619/25000000000000000000)
  centralHi := (542914042641504274477/100000000000000000000)
  directionLo := (54519042177694095851/10000000000000000000)
  directionHi := (545190421776940958511/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree121.table
  base := (7746428773491131595190882112260458731679/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27500000000000000000000000000000000000000
      center := (126)
      previous := (0)
      next := (105)
      square := (1710094006430919848227301120000000000000)
      linear := (-233756609072653812469999579465000000000000)
      constant := (8149188139798869659236047972439730092096938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree121.table
  base := (1239428603699365325654658979760229413249/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1337573879262251145512291341430070000000000000)
      constant := (46833947064580989114956107954923415682191948025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54519042177694095851/10000000000000000000)
  centralHi := (545190421776940958511/100000000000000000000)
  directionLo := (547457335595474905143/100000000000000000000)
  directionHi := (68432166949434363143/12500000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree122.table
  base := (31925106105268322291664265498006794904359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-5183687655752725950697445975110000000000000)
      constant := (182212078039402285397058618228418822183427439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree122.table
  base := (31925106104020506975106108066807759368203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1348250462533673859284732989767990000000000000)
      constant := (47599323463531143033689696709493560293246431787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547457335595474905143/100000000000000000000)
  centralHi := (68432166949434363143/12500000000000000000)
  directionLo := (109942980239262950607/20000000000000000000)
  directionHi := (137428725299078688259/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree123.table
  base := (65753227728692619350075708412517732208861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-10449459823814136054109802403980000000000000)
      constant := (370331739629770422274213107020834645597272181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree123.table
  base := (32876613863294603600559689588773650374487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-150991893978344063673019404233990000000000000)
      constant := (5374547830775847746129512038767131076953589247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109942980239262950607/20000000000000000000)
  centralHi := (137428725299078688259/25000000000000000000)
  directionLo := (27598161664196573239/5000000000000000000)
  directionHi := (551963233283931464781/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree124.table
  base := (33840238368879777507810707368122452455573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-5265772168061410103412356428870000000000000)
      constant := (188143514401743345689544957187782816747124333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree124.table
  base := (13536095347197367307322656727256022174197/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-2739207258153038573659232572887660000000000000)
      constant := (98297536209725970067178491217496139593477089065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27598161664196573239/5000000000000000000)
  centralHi := (551963233283931464781/100000000000000000000)
  directionLo := (27710122211803280139/5000000000000000000)
  directionHi := (554202444236065602781/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree125.table
  base := (69631959233206198889935928262842943845137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-10613628848431504359539623311500000000000000)
      constant := (382290023599405096533254062194803996205261577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree125.table
  base := (69631959231712280234633785938099319861489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-2760560424695884001204115869563500000000000000)
      constant := (99865672694202760090990794740092213591940588881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27710122211803280139/5000000000000000000)
  centralHi := (554202444236065602781/100000000000000000000)
  directionLo := (278216322084635726603/50000000000000000000)
  directionHi := (556432644169271453207/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree126.table
  base := (8950959401325238855180471791594225067603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-2673928340185047128063633441315000000000000)
      constant := (97085181004247382570196229511185802466359926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree126.table
  base := (35803837604671512478095210205761125281349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-154550755068818301597166620346630000000000000)
      constant := (5635903911514282032298383053698594477104375869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278216322084635726603/50000000000000000000)
  centralHi := (556432644169271453207/100000000000000000000)
  directionLo := (111730788200421233229/20000000000000000000)
  directionHi := (279326970501053083073/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree127.table
  base := (36803812332805860271386867219767293392581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-5388898936524436332484722109510000000000000)
      constant := (197219565027857730606035282243051842500502301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree127.table
  base := (2944304986582038292971992541395396561307/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-2803266757781574856293882462915180000000000000)
      constant := (103039329348753324074331279787883389471729675075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111730788200421233229/20000000000000000000)
  centralHi := (279326970501053083073/50000000000000000000)
  directionLo := (560866440516066510641/100000000000000000000)
  directionHi := (280433220258033255321/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree128.table
  base := (75631807593991907621189262320046807424847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-10859882385357556817684354672780000000000000)
      constant := (400585241715069399162009879421045663698406487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree128.table
  base := (75631807593098142002929569917702310439993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-2824619924324420283838765759591020000000000000)
      constant := (104644849518558732293729390288829775683774540697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560866440516066510641/100000000000000000000)
  centralHi := (280433220258033255321/50000000000000000000)
  directionLo := (2815351232071853011/500000000000000000)
  directionHi := (563070246414370602201/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree129.table
  base := (77680223991586028133626834668873443891703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-10941966897666240970399265126540000000000000)
      constant := (406779058994548414413492176529613686710896063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree129.table
  base := (9710027998854126916741381941415207384347/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8702500000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (541167021489639271970839563520000000000000)
      linear := (-79054808079646269760656918229635000000000000)
      constant := (2951745303237312136158863553164727673809823814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2815351232071853011/500000000000000000)
  centralHi := (563070246414370602201/100000000000000000000)
  directionLo := (282632730189338512893/50000000000000000000)
  directionHi := (565265460378677025787/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree130.table
  base := (15950574770864264595638021875408577639479/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-11024051409974925123114175580300000000000000)
      constant := (413020581893659703115187998416622189471884795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree130.table
  base := (9969109231710866863966363083503613762973/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-716831564352527784732133088235675000000000000)
      constant := (26973318385644842850094041172231919431160362234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282632730189338512893/50000000000000000000)
  centralHi := (565265460378677025787/100000000000000000000)
  directionLo := (567452182123829129057/100000000000000000000)
  directionHi := (283726091061914564529/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree131.table
  base := (81849757178205454065643336359014435011741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-11106135922283609275829086034060000000000000)
      constant := (419309810411920192358299819321720746636420661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree131.table
  base := (40924878588835517475437334247209004733791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1444339711976478283236707824809270000000000000)
      constant := (54768088698271084306754059093160220909304938239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567452182123829129057/100000000000000000000)
  centralHi := (283726091061914564529/50000000000000000000)
  directionLo := (71203813681338485007/12500000000000000000)
  directionHi := (569630509450707880057/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree132.table
  base := (4198543697966176131461975560319399787383/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27500000000000000000000000000000000000000
      center := (126)
      previous := (0)
      next := (105)
      square := (1710094006430919848227301120000000000000)
      linear := (-254277737149824850648727192905000000000000)
      constant := (9673789648837640440728437538897566988306065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree132.table
  base := (83970873958873345233226807643902323187121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-323336954499533554890922105143820000000000000)
      constant := (12354615830923230047350108899254743987014368201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71203813681338485007/12500000000000000000)
  centralHi := (569630509450707880057/100000000000000000000)
  directionLo := (571800538297272553329/100000000000000000000)
  directionHi := (57180053829727255333/10000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree133.table
  base := (86116224193835331219547131490913840213321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-11270304946900977581258906941580000000000000)
      constant := (432031384304003000325061083792120574665811841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree133.table
  base := (43058112096728069031407689290151181627373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1465692878519323710781591121485110000000000000)
      constant := (56429684393879922333658822695399736369203968717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571800538297272553329/100000000000000000000)
  centralHi := (57180053829727255333/10000000000000000000)
  directionLo := (286981181393932306229/50000000000000000000)
  directionHi := (573962362787864612459/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree134.table
  base := (44142903938986428469516545026304746583723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-5676194729604830866986908697670000000000000)
      constant := (219231864838452362193363904798622874336630483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree134.table
  base := (220714519694133683046218691019414672779/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-738184730895373212277016384911515000000000000)
      constant := (28634914081194127048954903680339654228349329100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286981181393932306229/50000000000000000000)
  centralHi := (573962362787864612459/100000000000000000000)
  directionLo := (576116075280846480313/100000000000000000000)
  directionHi := (288058037640423240157/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree135.table
  base := (4523981250401895425412938049192042638057/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-2858618492879586471672181962275000000000000)
      constant := (111235945166778467608059838848011185796024485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree135.table
  base := (90479625007768915554488666198196977599923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-330454676680482030739216537369100000000000000)
      constant := (12914711676582583932775060821456423679025331963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576116075280846480313/100000000000000000000)
  centralHi := (288058037640423240157/50000000000000000000)
  directionLo := (578261766414643417063/100000000000000000000)
  directionHi := (72282720801830427133/12500000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree136.table
  base := (92697675580399943979958549219366998933471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-11516558483827030039403638302860000000000000)
      constant := (451471537274191142885976584173623406870949991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree136.table
  base := (92697675580173403804542121904810920637811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-2995445256667183704197832132997740000000000000)
      constant := (117937615081046391404374256722827341332661980819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578261766414643417063/100000000000000000000)
  centralHi := (72282720801830427133/12500000000000000000)
  directionLo := (580399525152253447189/100000000000000000000)
  directionHi := (58039952515225344719/10000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree137.table
  base := (94939959591494029461425351762132058392503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-11598642996135714192118548756620000000000000)
      constant := (458046999497705184746921936479337979065492863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree137.table
  base := (9493995959130325241946479538609482489137/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1508399211605014565871357714836790000000000000)
      constant := (59827643150037134759722693497645872384510865365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580399525152253447189/100000000000000000000)
  centralHi := (58039952515225344719/10000000000000000000)
  directionLo := (582529438824287178499/100000000000000000000)
  directionHi := (1165058877648574357/200000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree138.table
  base := (97206477037818922180320258785248797560237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-11680727508444398344833459210380000000000000)
      constant := (464670167337232345639622404220135104504788677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree138.table
  base := (48603238518829135507517968413542775358519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-168786199430715253293755484797190000000000000)
      constant := (6743634374789846237535649241086002401023004639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582529438824287178499/100000000000000000000)
  centralHi := (1165058877648574357/200000000000000000)
  directionLo := (584651593170596427177/100000000000000000000)
  directionHi := (292325796585298213589/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree139.table
  base := (49748613957967631863468964368731797632717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-5881406010376541248774184832070000000000000)
      constant := (235670520396178231598251820534156547513558757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree139.table
  base := (12437153489474998538999292747250843953001/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-764876189073929996708120505756315000000000000)
      constant := (30782003104841888951563795121913748380407136658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584651593170596427177/100000000000000000000)
  centralHi := (292325796585298213589/50000000000000000000)
  directionLo := (586766072380547792807/100000000000000000000)
  directionHi := (73345759047568474101/12500000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree140.table
  base := (12726526527807983925580215922124002409249/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-2961224133265441662565820029475000000000000)
      constant := (119514904965667164077818153570154008583038258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree140.table
  base := (50906106111174984692899500880066041380153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1540428961419282707188682659850550000000000000)
      constant := (62441533659709698561767462083092589010398813337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586766072380547792807/100000000000000000000)
  centralHi := (73345759047568474101/12500000000000000000)
  directionLo := (294436479565997353259/50000000000000000000)
  directionHi := (588872959131994706519/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree141.table
  base := (104151429954084117384521055071339141431903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-11926981045370450802978190571660000000000000)
      constant := (484825904547767129016631141301512036113260263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree141.table
  base := (10415142995398821667043102678746322292783/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17405000000000000000000000000000000000000000
      center := (80122)
      previous := (0)
      next := (66080)
      square := (1082334042979278543941679127040000000000000)
      linear := (-172345060521189491217902700909830000000000000)
      constant := (7036143524792708001318617310531369739505888115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294436479565997353259/50000000000000000000)
  centralHi := (588872959131994706519/100000000000000000000)
  directionLo := (590972334628998994651/100000000000000000000)
  directionHi := (147743083657249748663/25000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree142.table
  base := (13314360138441548355574450416094806225401/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-3002266389419783738923275256355000000000000)
      constant := (122909973711814245979779901200874943106547042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree142.table
  base := (53257440553725823264213993451705290877181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1561782127962128134733565956526390000000000000)
      constant := (64215280399906683679788841141708815057891203549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590972334628998994651/100000000000000000000)
  centralHi := (147743083657249748663/25000000000000000000)
  directionLo := (593064278638350651409/100000000000000000000)
  directionHi := (59306427863835065141/10000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree143.table
  base := (54451282839800303761766175159849381594687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55000000000000000000000000000000000000000
      center := (252)
      previous := (0)
      next := (210)
      square := (3420188012861839696454602240000000000000)
      linear := (-549597730453991777654909612690000000000000)
      constant := (22659163216397729285232577688418343197541557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree143.table
  base := (108902565679532634350665158709975789347867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-3144917422467101697012015209728620000000000000)
      constant := (130222999379952775459683367788408211504479325243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593064278638350651409/100000000000000000000)
  centralHi := (59306427863835065141/10000000000000000000)
  directionLo := (595148869524932288827/100000000000000000000)
  directionHi := (148787217381233072207/25000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree144.table
  base := (27828620916783711042964690042305313786259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-3043308645574125815280730483235000000000000)
      constant := (126352748071966170979859069371438942968137339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree144.table
  base := (13914310458384702764918938721108431183729/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8702500000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (541167021489639271970839563520000000000000)
      linear := (-87951960805831864571024958511235000000000000)
      constant := (3667441644071893625136466468035476897901121298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595148869524932288827/100000000000000000000)
  centralHi := (148787217381233072207/25000000000000000000)
  directionLo := (597226184285972623793/100000000000000000000)
  directionHi := (298613092142986311897/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree145.table
  base := (14218829383379244033983080477313305881487/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-3063829773651296853459458096675000000000000)
      constant := (128092024857056416091358844237259820023319854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree145.table
  base := (113750635066985783185747580670712976292847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-3187623755552792552101781803080300000000000000)
      constant := (133845260219622406697187598942188266834278603663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597226184285972623793/100000000000000000000)
  centralHi := (298613092142986311897/50000000000000000000)
  directionLo := (299648149292115681439/50000000000000000000)
  directionHi := (599296298584231362879/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree146.table
  base := (4648440795049931445896387769074327745297/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-12337403606913871566552742840460000000000000)
      constant := (519372912181463978486301030383129841429523425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree146.table
  base := (14526377484525967463108331052223564069499/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-802244230523909494911666274939035000000000000)
      constant := (33918770619739987519500549255586454077466668342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299648149292115681439/50000000000000000000)
  centralHi := (599296298584231362879/100000000000000000000)
  directionLo := (300679643390077974997/50000000000000000000)
  directionHi := (120271857356031189999/20000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree147.table
  base := (59347819045889228609490162146321990633827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-6209744059611277859633826647110000000000000)
      constant := (263212715273608350131956046874364960866693067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree147.table
  base := (14836954761468041094186060597037295744249/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8702500000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (541167021489639271970839563520000000000000)
      linear := (-89731391351068983533098566567555000000000000)
      constant := (3819926832347412218670417237761478652971461538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300679643390077974997/50000000000000000000)
  centralHi := (120271857356031189999/20000000000000000000)
  directionLo := (603415221963048843343/100000000000000000000)
  directionHi := (37713451372690552709/6250000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree148.table
  base := (121204489710674138696221151661865817301373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-12501572631531239871982563747980000000000000)
      constant := (533525654525126840156635565781005763893466133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree148.table
  base := (60602244855322706826211214350174062250201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1625841627590664417368215846553910000000000000)
      constant := (69686055338085325623781852666741843196236547129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603415221963048843343/100000000000000000000)
  centralHi := (37713451372690552709/6250000000000000000)
  directionLo := (605464175981282281259/100000000000000000000)
  directionHi := (30273208799064114063/5000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree149.table
  base := (123737574730032913455427302664358792975393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-12583657143839924024697474201740000000000000)
      constant := (540673584114843205692503156765867413950022553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree149.table
  base := (61868787365004368716760249518227831636641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1636518210862087131140657494891830000000000000)
      constant := (70619658306930229697866571621499869737344325889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (605464175981282281259/100000000000000000000)
  centralHi := (30273208799064114063/5000000000000000000)
  directionLo := (607506219471595875921/100000000000000000000)
  directionHi := (303753109735797937961/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree150.table
  base := (7893430821687447639761967107467611795773/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-3166435414037152044353096163875000000000000)
      constant := (136967304829005066735251395742514324109154132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree150.table
  base := (126294893146978815748509310652899783658481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-366043287585224409980688698495500000000000000)
      constant := (15902109308609644983055141933907744146915172361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607506219471595875921/100000000000000000000)
  centralHi := (303753109735797937961/50000000000000000000)
  directionLo := (121908284377502166973/20000000000000000000)
  directionHi := (304770710943755417433/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree151.table
  base := (64438222479381494810258727796943578675663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-6373913084228646165063647554630000000000000)
      constant := (277556280064159013278282651538170173019755223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree151.table
  base := (128876444958745866820382069938915831930701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-3315742754809865117371081583135340000000000000)
      constant := (145011112166961659949561261982961914098556931629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121908284377502166973/20000000000000000000)
  centralHi := (304770710943755417433/50000000000000000000)
  directionLo := (611569851526893147867/100000000000000000000)
  directionHi := (152892462881723286967/25000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree152.table
  base := (26296446032511837107679894548425417605711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-12829910680765976482842205563020000000000000)
      constant := (562403606551401894120711618243717377651455155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree152.table
  base := (65741115081272388148649824896694937702561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1668547960676355272457982439905590000000000000)
      constant := (73457850891099198217199664481712795703283533569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611569851526893147867/100000000000000000000)
  centralHi := (152892462881723286967/25000000000000000000)
  directionLo := (613591575558696687057/100000000000000000000)
  directionHi := (306795787779348343529/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree153.table
  base := (134112248755666220283820526010590451322163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-12911995193074660635557116016780000000000000)
      constant := (569742358584942564539016471574601444609981723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree153.table
  base := (134112248755654095090772741166205312554969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-373161009766172885828983130720780000000000000)
      constant := (16536972513679083780390799642592180693003847089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613591575558696687057/100000000000000000000)
  centralHi := (306795787779348343529/50000000000000000000)
  directionLo := (615606660048915846777/100000000000000000000)
  directionHi := (307803330024457923389/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree154.table
  base := (17095812591925658903846339897400173208349/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27500000000000000000000000000000000000000
      center := (126)
      previous := (0)
      next := (105)
      square := (1710094006430919848227301120000000000000)
      linear := (-295319993304166927006182419785000000000000)
      constant := (13116564005195815915312106036962803810583678) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree154.table
  base := (17095812591924383558780292971742803424297/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-844950563609600350001432868290715000000000000)
      constant := (37690566172404452502490295630698690576959601426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615606660048915846777/100000000000000000000)
  centralHi := (307803330024457923389/50000000000000000000)
  directionLo := (617615169985776093063/100000000000000000000)
  directionHi := (77201896248222011633/12500000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree155.table
  base := (69722493049569639807815523344788296799299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-6538082108846014470493468462150000000000000)
      constant := (292281489741051408607231150363219383912715179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree155.table
  base := (139444986099130694850006105459642584227027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-3401155420981246827550614769838700000000000000)
      constant := (152704237981633949771052817191095642521248528883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617615169985776093063/100000000000000000000)
  centralHi := (77201896248222011633/12500000000000000000)
  directionLo := (619617169304189597101/100000000000000000000)
  directionHi := (309808584652094798551/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree156.table
  base := (142147704844272035904630725294511336893667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-13158248730000713093701847378060000000000000)
      constant := (592044848345089174007619112101915871764133707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree156.table
  base := (142147704844264812845902876635355496439037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-380278731947121361677277562946060000000000000)
      constant := (17184296944342093129643079570310152483104287797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (619617169304189597101/100000000000000000000)
  centralHi := (309808584652094798551/50000000000000000000)
  directionLo := (621612720909501989229/100000000000000000000)
  directionHi := (62161272090950198923/10000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree157.table
  base := (144874656968247292396859987495491392006869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-13240333242309397246416757831820000000000000)
      constant := (599574422817265664681393017885474458432831149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree157.table
  base := (144874656968241215301746366176845578159797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-3443861754066937682640381363190380000000000000)
      constant := (156625568241872391783169719033250775118168280213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621612720909501989229/100000000000000000000)
  centralHi := (62161272090950198923/10000000000000000000)
  directionLo := (77950235837569398359/12500000000000000000)
  directionHi := (623601886700555186873/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree158.table
  base := (73812921234273950913843329983135807471537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-6661208877309040699565834142790000000000000)
      constant := (303575851449163857208381762552319432704055977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree158.table
  base := (5905033698741711563684280731161443974681/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-3465214920609783110185264659866220000000000000)
      constant := (158604925209935751983092243338656601957069526225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77950235837569398359/12500000000000000000)
  centralHi := (623601886700555186873/100000000000000000000)
  directionLo := (625584727592090218329/100000000000000000000)
  directionHi := (62558472759209021833/10000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree159.table
  base := (37600315335673745209264430255009034944523/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-3351125566731691387961644684835000000000000)
      constant := (153694172146993844581791054533826093228287283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree159.table
  base := (7520063067134533980056450372301170423181/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8702500000000000000000000000000000000000000
      center := (40061)
      previous := (0)
      next := (33040)
      square := (541167021489639271970839563520000000000000)
      linear := (-96849113532017459381392998792835000000000000)
      constant := (4461020650088646075841531719223546871215465305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625584727592090218329/100000000000000000000)
  centralHi := (62558472759209021833/10000000000000000000)
  directionLo := (627561303536512981691/100000000000000000000)
  directionHi := (156890325884128245423/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree160.table
  base := (1532009135882470972543030402993237522669/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-3371646694808862426140372298275000000000000)
      constant := (155612344971478310779986002801054543506073725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree160.table
  base := (3830022839706086971467100475299015443627/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-876980313423868491318757813304475000000000000)
      constant := (40650255705390606288620566180814428548333902830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627561303536512981691/100000000000000000000)
  centralHi := (156890325884128245423/25000000000000000000)
  directionLo := (629531673545044941851/100000000000000000000)
  directionHi := (157382918386261235463/25000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree161.table
  base := (31204959840559896045517106685477365640667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-13568671291544133857276399646860000000000000)
      constant := (630169776791850331522030617101793806212603535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree161.table
  base := (78012399601398218193516670665705337942473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (721098)
      previous := (0)
      next := (594720)
      square := (9741006386813506895475112143360000000000000)
      linear := (-1764637210119159696409957274946870000000000000)
      constant := (82308881732486956413968267867573392532399736617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629531673545044941851/100000000000000000000)
  centralHi := (157382918386261235463/25000000000000000000)
  directionLo := (631495895708279876061/100000000000000000000)
  directionHi := (315747947854139938031/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree162.table
  base := (158872918183983252293640083905855815396837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-13650755803852818009991310100620000000000000)
      constant := (637937879305500009360368956731728553663017277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree162.table
  base := (158872918183980691874739898469419298313681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-394514176309018313373866427396620000000000000)
      constant := (18516329481483500858440104752860968577429923561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631495895708279876061/100000000000000000000)
  centralHi := (315747947854139938031/50000000000000000000)
  directionLo := (25338161088646677099/4000000000000000000)
  directionHi := (158363506804041731869/25000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree163.table
  base := (6469810821178587301729725241805422412799/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-13732840316161502162706220554380000000000000)
      constant := (645753687426579895194942979250581402798716975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree163.table
  base := (161745270529462528851058633402568039454947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-3571980753324010247909681143245420000000000000)
      constant := (168688628426622096845243513953576834108084034563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25338161088646677099/4000000000000000000)
  centralHi := (158363506804041731869/25000000000000000000)
  directionLo := (635406124377439414493/100000000000000000000)
  directionHi := (317703062188719707247/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree164.table
  base := (20580232029618057511384912600984156968173/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-3453731207117546578855282752035000000000000)
      constant := (163404300288702943102157381099958165986297866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree164.table
  base := (41160464059235662146116115538871291516313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-898333479966713918863641109980315000000000000)
      constant := (42685688186178411363956074978191678691914569977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (635406124377439414493/100000000000000000000)
  centralHi := (317703062188719707247/50000000000000000000)
  directionLo := (318676121319254034661/50000000000000000000)
  directionHi := (637352242638508069323/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree165.table
  base := (83781337652078493553129310578528215234667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55000000000000000000000000000000000000000
      center := (252)
      previous := (0)
      next := (210)
      square := (3420188012861839696454602240000000000000)
      linear := (-631682242762675930369820066450000000000000)
      constant := (30069473658632795621085950252863810367581337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree165.table
  base := (6702507012166218538968338025268797043219/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-401631898489966789222160859621900000000000000)
      constant := (19201037587506130551528826366334517062686133475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318676121319254034661/50000000000000000000)
  centralHi := (637352242638508069323/100000000000000000000)
  directionLo := (9988944321903697503/1562500000000000000)
  directionHi := (639292436601836640193/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree166.table
  base := (170507727728869690702488552989029832328401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-13979093853087554620850951915660000000000000)
      constant := (669487345431638947641485725508552609711736521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree166.table
  base := (170507727728868409244557252807418894027893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-3636040252952546530544331033272940000000000000)
      constant := (174888385055076741362854476108727346530999859797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9988944321903697503/1562500000000000000)
  centralHi := (639292436601836640193/100000000000000000000)
  directionLo := (641226760043817086181/100000000000000000000)
  directionHi := (320613380021908543091/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree167.table
  base := (86738506754441176512742562102317953352397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2772)
      previous := (0)
      next := (2310)
      square := (37622068141480236661000624640000000000000)
      linear := (-7030589182698119386782931184710000000000000)
      constant := (338746987989848938990522811806240472355640037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree167.table
  base := (173477013508881275288276220531917256135809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1442196)
      previous := (0)
      next := (1189440)
      square := (19482012773627013790950224286720000000000000)
      linear := (-3657393419495391958089214329948780000000000000)
      constant := (176979893047209414254995362056004615717478760161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641226760043817086181/100000000000000000000)
  centralHi := (320613380021908543091/50000000000000000000)
  directionLo := (643155265932160919981/100000000000000000000)
  directionHi := (321577632966080459991/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree168.table
  base := (176470532642026458910187303485304986102711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (5544)
      previous := (0)
      next := (4620)
      square := (75244136282960473322001249280000000000000)
      linear := (-14143262877704922926280772823180000000000000)
      constant := (685548312133835904347598215085241903318428031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree168.table
  base := (176470532642025552539484590288239422841037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (160244)
      previous := (0)
      next := (132160)
      square := (2164668085958557087883358254080000000000000)
      linear := (-408749620670915265070455291847180000000000000)
      constant := (19898206918209472935517457410957681430909649797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell214.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643155265932160919981/100000000000000000000)
  centralHi := (321577632966080459991/50000000000000000000)
  directionLo := (322539003221411305249/50000000000000000000)
  directionHi := (645078006442822610499/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree169.table
  base := (8974414256308228025609737092357986697881/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1386)
      previous := (0)
      next := (1155)
      square := (18811034070740118330500312320000000000000)
      linear := (-3556336847503401769748920819235000000000000)
      constant := (173412588473448598887992764424946581952218005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree169.table
  base := (22436035640770474785834619360259841254877/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78322500000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (4870503193406753447737556071680000000000000)
      linear := (-925024938145270703294745230825115000000000000)
      constant := (45300073176259325978532746783645116133348083066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell214.Kernel169
