import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell124.Parameters
import ForestUnimodality.BinomialMassData.Q111_211.Batch000_049
import ForestUnimodality.BinomialMassData.Q111_211.Batch050_099
import ForestUnimodality.BinomialMassData.Q111_211.Batch100_149
import ForestUnimodality.BinomialMassData.Q23557_44732.Batch000_049
import ForestUnimodality.BinomialMassData.Q23557_44732.Batch050_099
import ForestUnimodality.BinomialMassData.Q23557_44732.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree000.table
  base := (4991298390530275579489938329/100000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (18407925247147863268004641600000000000)
      linear := (-1002706307640962961336139620000000000)
      constant := (9982596781060551158979876658000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree000.table
  base := (4991298390530275579489938329/100000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (18407925247147863268004641600000000000)
      linear := (-1002706307640962961336139620000000000)
      constant := (9982596781060551158979876658000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree001.table
  base := (6933831217622246066189810595706211352093/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44521000000000000000000000000000000000000000
      center := (445210)
      previous := (222605)
      next := (222605)
      square := (4097696199641350102774173243368000000000000)
      linear := (-4534527609746917616007598469246100000000000)
      constant := (1236055840716046907535558924701713042426129812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree001.table
  base := (138559316170502937055033363791415651525451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-63751770225157599965241125471502974500000000000)
      constant := (17345769393436856030620991116164304377749972554539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49929059361808908931/100000000000000000000)
  directionHi := (12482264840452227233/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree002.table
  base := (16199739865657669654402380829281803897381/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44521000000000000000000000000000000000000000
      center := (445210)
      previous := (222605)
      next := (222605)
      square := (4097696199641350102774173243368000000000000)
      linear := (-8845847781881418672006965578382100000000000)
      constant := (725999543342659877085324637943927391315299501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree002.table
  base := (20219292281397182324246800042309296017673/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-124368591989048809345166641490259594500000000000)
      constant := (10181604024531420898450688222327808327429681396388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49929059361808908931/100000000000000000000)
  centralHi := (12482264840452227233/25000000000000000000)
  directionLo := (35305176453000754351/50000000000000000000)
  directionHi := (70610352906001508703/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree003.table
  base := (25130195576734299461348009275208447299899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-65785839770079598640031663437590500000000000)
      constant := (2290435113944194402399302638895672064477606758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree003.table
  base := (100327814441371893811185281716040963440961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-369970827505880037450184315018032429000000000000)
      constant := (12844151996251163932333809618710318929244264328929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35305176453000754351/50000000000000000000)
  centralHi := (70610352906001508703/100000000000000000000)
  directionLo := (21619916897193883463/25000000000000000000)
  directionHi := (86479667588775533853/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree004.table
  base := (33270543033960474437283387577456992613271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-87342440630752103920028498983270500000000000)
      constant := (1574307903646123711104073146601404768135438191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree004.table
  base := (13280090677486289180735578261700996697429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 250118978000000000000000000000000000000000000000
      center := (2501189780)
      previous := (1250594890)
      next := (1250594890)
      square := (23020857249585104877385305281241424000000000000)
      linear := (-98240894206732491242007069411109133800000000000)
      constant := (1765594376319191423171423372753303763971158353781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21619916897193883463/25000000000000000000)
  centralHi := (86479667588775533853/100000000000000000000)
  directionLo := (49929059361808908931/50000000000000000000)
  directionHi := (99858118723617817863/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree005.table
  base := (73091903783478233657004104422168156753/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 44521000000000000000000000000000000000000000
      center := (445210)
      previous := (222605)
      next := (222605)
      square := (4097696199641350102774173243368000000000000)
      linear := (-21779808298284921840005066905790100000000000)
      constant := (237201592976076081954754694705878804435220032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree005.table
  base := (46678302069821909303498109802467400630883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-612438114561444874969886379093058909000000000000)
      constant := (6652132733684266581122001243045503075806505598787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49929059361808908931/50000000000000000000)
  centralHi := (99858118723617817863/100000000000000000000)
  directionLo := (4465790831425079499/4000000000000000000)
  directionHi := (27911192696406746869/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree006.table
  base := (8629700555038802108381114446802410185467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-130455642352097114480022170074630500000000000)
      constant := (976052096759551807354665921716423207734352614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree006.table
  base := (1722286857300618226151353619207855697027/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 125059489000000000000000000000000000000000000000
      center := (1250594890)
      previous := (625297445)
      next := (625297445)
      square := (11510428624792552438692652640620712000000000000)
      linear := (-73367175808922729372973741113057214900000000000)
      constant := (547678212898270357030670569617697765161870878406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4465790831425079499/4000000000000000000)
  centralHi := (27911192696406746869/25000000000000000000)
  directionLo := (122300718773563334747/100000000000000000000)
  directionHi := (30575179693390833687/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree007.table
  base := (3292922943314412796435647731562923115539/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-152012243212769619760019005620310500000000000)
      constant := (868361614251057520879229649397815100107647276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree007.table
  base := (13144114978137074158872307808551706878209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-427452700808504856244794221584042694500000000000)
      constant := (2437450429064873289699228266799715816891602775201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122300718773563334747/100000000000000000000)
  centralHi := (30575179693390833687/25000000000000000000)
  directionLo := (33024968566681922891/25000000000000000000)
  directionHi := (26419974853345538313/20000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree008.table
  base := (20493118575712070834755808780202602384823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-347137688146884250080031682331981000000000000)
      constant := (1647540836186128937681417458410928060774704783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree008.table
  base := (20449540670520079768803980258384986450499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-976139045144792131249439475205598629000000000000)
      constant := (4626854465413245937235727575087098672771328735011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33024968566681922891/25000000000000000000)
  centralHi := (26419974853345538313/20000000000000000000)
  directionLo := (35305176453000754351/25000000000000000000)
  directionHi := (28244141162400603481/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree009.table
  base := (8022940066982598392362799392802528155937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-195125444934114630320012676711670500000000000)
      constant := (821751496333635903801108788162005856030471177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree009.table
  base := (16009940633163361719462605360221091558221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-1097372688672574550009290507243111869000000000000)
      constant := (4617622155146859796249641243959163682043332009069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35305176453000754351/25000000000000000000)
  centralHi := (28244141162400603481/20000000000000000000)
  directionLo := (74893589042713363397/50000000000000000000)
  directionHi := (29957435617085345359/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree010.table
  base := (12505030403259044115687503140776053756511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-433364091589574271200019024514701000000000000)
      constant := (1702498885649669516458676136118500689293626231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree010.table
  base := (12474372096645445765658879041133870217983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-1218606332200356968769141539280625109000000000000)
      constant := (4785292258395425095446486833801677067553272590687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74893589042713363397/50000000000000000000)
  centralHi := (29957435617085345359/20000000000000000000)
  directionLo := (31577909802613838313/20000000000000000000)
  directionHi := (78944774506534595783/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree011.table
  base := (959235802522640312052870096698762609083/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44521000000000000000000000000000000000000000
      center := (445210)
      previous := (222605)
      next := (222605)
      square := (4097696199641350102774173243368000000000000)
      linear := (-47647729331091928176001269560606100000000000)
      constant := (181214226724745552088042323945254710118984243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree011.table
  base := (191311837564592309129428828457553244759/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25011897800000000000000000000000000000000000000
      center := (250118978)
      previous := (125059489)
      next := (125059489)
      square := (2302085724958510487738530528124142400000000000)
      linear := (-26796799514562787750579851426362766980000000000)
      constant := (101903857687943089078722909981122686984852468151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31577909802613838313/20000000000000000000)
  centralHi := (78944774506534595783/50000000000000000000)
  directionLo := (10349747252406361673/6250000000000000000)
  directionHi := (165595956038501786769/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree012.table
  base := (892951983601201836745023894784303042271/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-259795247516132146160003183348710500000000000)
      constant := (982560345469405889920443634043733822979788764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree012.table
  base := (177997942889065065957197942840604098361/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 125059489000000000000000000000000000000000000000
      center := (1250594890)
      previous := (625297445)
      next := (625297445)
      square := (11510428624792552438692652640620712000000000000)
      linear := (-146107361925592180628884360335565158900000000000)
      constant := (552685401306378421894788014418000649269329590116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10349747252406361673/6250000000000000000)
  centralHi := (165595956038501786769/100000000000000000000)
  directionLo := (21619916897193883463/12500000000000000000)
  directionHi := (34591867035510213541/20000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree013.table
  base := (2527761666901031292343898971336651257813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-281351848376804651440000018894390500000000000)
      constant := (1078418000560969765608100111239845550649092573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree013.table
  base := (5034386567171096689262667804088022718847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-1582307262783704225048694635393164829000000000000)
      constant := (6067399139042776356975402780228163147989396489183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21619916897193883463/12500000000000000000)
  centralHi := (34591867035510213541/20000000000000000000)
  directionLo := (180021783664687346863/100000000000000000000)
  directionHi := (11251361479042959179/6250000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree014.table
  base := (1629315176883632762974884774728372276347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-302908449237477156719996854440070500000000000)
      constant := (1192098105694510096264431076022328862115244787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree014.table
  base := (1619860857917261976762675998463217240067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-851770453155743321904272833715339034500000000000)
      constant := (3354082275739464213164353437197249287588769345763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180021783664687346863/100000000000000000000)
  centralHi := (11251361479042959179/6250000000000000000)
  directionLo := (186817433775786915807/100000000000000000000)
  directionHi := (5838044805493341119/3125000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree015.table
  base := (106451061575846155090187211775795226039/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-324465050098149661999993689985750500000000000)
      constant := (1322493870067930227138811135097768934067858552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree015.table
  base := (1686295871497860409391614920095655224063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-1824774549839269062568396699468191309000000000000)
      constant := (7442943886837504340973222024556817264691499283807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186817433775786915807/100000000000000000000)
  centralHi := (5838044805493341119/3125000000000000000)
  directionLo := (96687207700043711349/50000000000000000000)
  directionHi := (193374415400087422699/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree016.table
  base := (351796894903163927851684519759795069513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-692043301917644334559981051062861000000000000)
      constant := (2937541658320383894606938248502321836289788273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree016.table
  base := (336671938927273729209015013879359194851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-1946008193367051481328247731505704549000000000000)
      constant := (8267055281118916694501053319654632532555517491139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96687207700043711349/50000000000000000000)
  centralHi := (193374415400087422699/100000000000000000000)
  directionLo := (7988649497889425429/4000000000000000000)
  directionHi := (99858118723617817863/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree017.table
  base := (-206251432807193371472209332672139575467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-367578251819494672559987361077110500000000000)
      constant := (1630275062662303208586029861801975847921267386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree017.table
  base := (-838499026873768327185109885830901560939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-2067241836894833900088098763543217789000000000000)
      constant := (9176828370259210058185432952564907737129666299829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7988649497889425429/4000000000000000000)
  centralHi := (99858118723617817863/50000000000000000000)
  directionLo := (205862785536472432847/100000000000000000000)
  directionHi := (12866424096029527053/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree018.table
  base := (-1850832895130252100311784916807257125603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-778269705360334355679968393245581000000000000)
      constant := (3612960575579802078274107441443162105511028837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree018.table
  base := (-1862843075009592225861946825614663831677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-2188475480422616318847949795580731029000000000000)
      constant := (10169308492630308456490322433618986809803692366947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205862785536472432847/100000000000000000000)
  centralHi := (12866424096029527053/6250000000000000000)
  directionLo := (211831058718004526107/100000000000000000000)
  directionHi := (52957764679501131527/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree019.table
  base := (-2745046305121276168768927460133705491391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-821382907081679366239962064336941000000000000)
      constant := (3993911006469855968549607284507886297817781289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree019.table
  base := (-1377855447534662818015363139480640700293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-1154854561975199368803900413809122134500000000000)
      constant := (5621037830440198981574327182859531559753755269723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211831058718004526107/100000000000000000000)
  centralHi := (52957764679501131527/25000000000000000000)
  directionLo := (217635724104168429593/100000000000000000000)
  directionHi := (108817862052084214797/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree020.table
  base := (-440459665403846741249941770391809346779/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-432248054401512188399977867714150500000000000)
      constant := (2201343842862939086940824124317555024288208564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree020.table
  base := (-706624960683505957096997295860293073011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 250118978000000000000000000000000000000000000000
      center := (2501189780)
      previous := (1250594890)
      next := (1250594890)
      square := (23020857249585104877385305281241424000000000000)
      linear := (-486188553495636231273530371931151501800000000000)
      constant := (2478625226462466042660671251978065843899004648621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217635724104168429593/100000000000000000000)
  centralHi := (108817862052084214797/50000000000000000000)
  directionLo := (4465790831425079499/2000000000000000000)
  directionHi := (223289541571253974951/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree021.table
  base := (-2100044919677827940014704185186150012377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-453804655262184693679974703259830500000000000)
      constant := (2419347819802884171038332771560777915298963583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree021.table
  base := (-2104220134785344709111530448673703682409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-1276088205502981787563751445846635374500000000000)
      constant := (6810394839366509273896850357716960978615512170999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4465790831425079499/2000000000000000000)
  centralHi := (223289541571253974951/100000000000000000000)
  directionLo := (22880369390343285037/10000000000000000000)
  directionHi := (228803693903432850371/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree022.table
  base := (-4785469922482528640892740738395012240329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-950722512245714397919943077611021000000000000)
      constant := (5301436853132173759715074965747057660048312591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree022.table
  base := (-4792835046230606453721981092561171796071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-2673410054533745993887353923730783989000000000000)
      constant := (14923668416101407249190671018286642444442148532281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22880369390343285037/10000000000000000000)
  centralHi := (228803693903432850371/100000000000000000000)
  directionLo := (58547011725947013077/25000000000000000000)
  directionHi := (234188046903788052309/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree023.table
  base := (-5289203875229147721134680746550390811401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-993835713967059408479936748702381000000000000)
      constant := (5790493438726249333800937916541573050685616079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree023.table
  base := (-5295687101497351248800530504791493894661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-2794643698061528412647204955768297229000000000000)
      constant := (16300589540519043217806462445859345615237075511771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58547011725947013077/25000000000000000000)
  centralHi := (234188046903788052309/100000000000000000000)
  directionLo := (239451356816715220311/100000000000000000000)
  directionHi := (29931419602089402539/12500000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree024.table
  base := (-5585136187490607498002425824528097559/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-518474457844202209519965209896870500000000000)
      constant := (3152757112748248551745393167367338499110789632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree024.table
  base := (-5724875892039829108225513698479627892579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-2915877341589310831407055987805810469000000000000)
      constant := (17750567651161315514037549155160140644843923367869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239451356816715220311/100000000000000000000)
  centralHi := (29931419602089402539/12500000000000000000)
  directionLo := (122300718773563334747/50000000000000000000)
  directionHi := (48920287509425333899/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree025.table
  base := (-760253871800227093408790410162989397003/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-540031058704874714799962045442550500000000000)
      constant := (3423101923671815593700253627896546696224117748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree025.table
  base := (-6087027568776476315944322065241701232729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-3037110985117093250166907019843323709000000000000)
      constant := (19272774084980327615534411475870515751094241184519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122300718773563334747/50000000000000000000)
  centralHi := (48920287509425333899/20000000000000000000)
  directionLo := (15602831050565284041/6250000000000000000)
  directionHi := (249645296809044544657/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree026.table
  base := (-1595835352505346523603913040903061744533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-561587659565547220079958880988230500000000000)
      constant := (3706156872217376394825544993633762576143292614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree026.table
  base := (-6387717210671395998728520935510307543839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-3158344628644875668926758051880836949000000000000)
      constant := (20866511625449694135919695228036454625834649561729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15602831050565284041/6250000000000000000)
  centralHi := (249645296809044544657/100000000000000000000)
  directionLo := (50917849596239228517/20000000000000000000)
  directionHi := (127294623990598071293/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree027.table
  base := (-6627810483797073024595771142325783947361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-1166288520852439450719911433067821000000000000)
      constant := (8003634680493536763319889347775260772879540919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree027.table
  base := (-3315818496603047270549426022818070595743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-1639789136086329043843304541959175094500000000000)
      constant := (11265596735750699778897499470104483353455454844673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50917849596239228517/20000000000000000000)
  centralHi := (127294623990598071293/50000000000000000000)
  directionLo := (259439002766326601557/100000000000000000000)
  directionHi := (129719501383163300779/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree028.table
  base := (-6819395129621142381549582514899187994257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-1209401722573784461279905104159181000000000000)
      constant := (8619990488866165585298805668131321251307684103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree028.table
  base := (-1705684182886450768230961189809899076309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-1700405957850220253223230057977931714500000000000)
      constant := (12133162830634617812746035846496095157250448907798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259439002766326601557/100000000000000000000)
  centralHi := (129719501383163300779/50000000000000000000)
  directionLo := (33024968566681922891/12500000000000000000)
  directionHi := (264199748533455383129/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree029.table
  base := (-3480713629505438961858809821742621947769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-626257462147564735919949387625270500000000000)
      constant := (4630616414759989132689153981259651228263376351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree029.table
  base := (-3482170845794150299328000454118363409491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-1761022779614111462603155573996688334500000000000)
      constant := (13035746169349618485239577441257569926367757789901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33024968566681922891/12500000000000000000)
  centralHi := (264199748533455383129/100000000000000000000)
  directionLo := (67219053332135718999/25000000000000000000)
  directionHi := (268876213328542875997/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree030.table
  base := (-882089083905093384316626122638407529243/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-647814063008237241199946223170950500000000000)
      constant := (4963618392732738119699865004062076833562289588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree030.table
  base := (-3529625762243596355780212176258132885167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-1821639601378002671983081090015444954500000000000)
      constant := (13973171690424377708377486389264101385536919300337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67219053332135718999/25000000000000000000)
  centralHi := (268876213328542875997/100000000000000000000)
  directionLo := (68368180218693081529/25000000000000000000)
  directionHi := (273472720874772326117/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree031.table
  base := (-3553807109484652893221168684392465358603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-669370663868909746479943058716630500000000000)
      constant := (5308948580069723968902098656098418549769635837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree031.table
  base := (-1777455859730190029991429797944946486281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-1882256423141893881363006606034201574500000000000)
      constant := (14945291998202509406768696054119697662211705259182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68368180218693081529/25000000000000000000)
  centralHi := (273472720874772326117/100000000000000000000)
  directionLo := (277993237384304320823/100000000000000000000)
  directionHi := (34749154673038040103/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree032.table
  base := (-7116121781393937775374014613808691565769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-1381854529459164503519879788524621000000000000)
      constant := (11333125362130146640174861141706975242800398351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree032.table
  base := (-7118042167309988870219912564071528972421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-3885746489811570181485864244105916389000000000000)
      constant := (31903965975745656912993998281606772195260334647131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277993237384304320823/100000000000000000000)
  centralHi := (34749154673038040103/12500000000000000000)
  directionLo := (282441411624006034809/100000000000000000000)
  directionHi := (28244141162400603481/10000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree033.table
  base := (-7083911160598859176698691989827168608123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-1424967731180509514079873459615981000000000000)
      constant := (12072846783052980959948884731300457626397755917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree033.table
  base := (-7085578845336345287199858817048735041703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-4006980133339352600245715276143429629000000000000)
      constant := (33986280327496295869764983905984890578338229130233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282441411624006034809/100000000000000000000)
  centralHi := (28244141162400603481/10000000000000000000)
  directionLo := (286820609386627322133/100000000000000000000)
  directionHi := (143410304693313661067/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree034.table
  base := (-7012393666057827976554183019295535473953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-1468080932901854524639867130707341000000000000)
      constant := (12836998589998869717825426485144057465164138487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree034.table
  base := (-7013840572787301812156087241118993897409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-4128213776867135019005566308180942869000000000000)
      constant := (36137351080476542371745975267335844698495912035999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286820609386627322133/100000000000000000000)
  centralHi := (143410304693313661067/50000000000000000000)
  directionLo := (72783485823395786547/25000000000000000000)
  directionHi := (291133943293583146189/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree035.table
  base := (-690275786529880012934431339640213082423/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44521000000000000000000000000000000000000000
      center := (445210)
      previous := (222605)
      next := (222605)
      square := (4097696199641350102774173243368000000000000)
      linear := (-151119413462319953519986080179870100000000000)
      constant := (1362552786675290078675847367950681573357445617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree035.table
  base := (-863001517023879309736295891580150309261/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-2124723710197458718882708670109228054500000000000)
      constant := (19178515032944304320086367929580550672247509489484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72783485823395786547/25000000000000000000)
  centralHi := (291133943293583146189/100000000000000000000)
  directionLo := (14769214933978915187/5000000000000000000)
  directionHi := (295384298679578303741/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree036.table
  base := (-6756004741273281504593562499447320954253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-1554307336344544545759854472890061000000000000)
      constant := (14438390048553090173930926967987421823795702187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree036.table
  base := (-844636391961262777673651763626342671029/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-2185340531961349928262634186127984674500000000000)
      constant := (20322596262184219963616674419229337353988872623276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14769214933978915187/5000000000000000000)
  centralHi := (295384298679578303741/100000000000000000000)
  directionLo := (74893589042713363397/25000000000000000000)
  directionHi := (299574356170853453589/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree037.table
  base := (-3286488649543700880746441280342175265953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-798710269032944778159924071990710500000000000)
      constant := (7637773801984553940392972983126864514984506487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree037.table
  base := (-3286958780127662855173164709591837493653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-2245957353725241137642559702146741294500000000000)
      constant := (21500866703662289882157700559257728795347715076683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74893589042713363397/25000000000000000000)
  centralHi := (299574356170853453589/100000000000000000000)
  directionLo := (151853305729523386411/50000000000000000000)
  directionHi := (303706611459046772823/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree038.table
  base := (-3177192749573889442581849051947002253361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-820266869893617283439920907536390500000000000)
      constant := (8068484462426845434003969866541246512678114919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree038.table
  base := (-6355198689358456754335379020883265740613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-4613148350978264694044970436330995829000000000000)
      constant := (45426564262747710680178784726801883192327731673243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151853305729523386411/50000000000000000000)
  centralHi := (303706611459046772823/100000000000000000000)
  directionLo := (307783392685004104969/100000000000000000000)
  directionHi := (30778339268500410497/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree039.table
  base := (-762603406854098406346907704641410158491/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-841823470754289788719917743082070500000000000)
      constant := (8511313695752660265019998988781298613335288756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree039.table
  base := (-6101530059977090500243654693993309645537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-4734381994506047112804821468368509069000000000000)
      constant := (47919610613087734021304895012731783503560371649407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307783392685004104969/100000000000000000000)
  centralHi := (30778339268500410497/10000000000000000000)
  directionLo := (77951718944102860401/25000000000000000000)
  directionHi := (62361375155282288321/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree040.table
  base := (-726600764506036367474944357876750821983/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-863380071614962293999914578627750500000000000)
      constant := (8966250292689318946055453301155896706617979428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree040.table
  base := (-116268262416321523374753598555791664871/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25011897800000000000000000000000000000000000000
      center := (250118978)
      previous := (125059489)
      next := (125059489)
      square := (2302085724958510487738530528124142400000000000)
      linear := (-97112312760676590631293450008120446180000000000)
      constant := (1009616194948517232646702566186596658600773489081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77951718944102860401/25000000000000000000)
  centralHi := (62361375155282288321/20000000000000000000)
  directionLo := (31577909802613838313/10000000000000000000)
  directionHi := (315779098026138383131/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree041.table
  base := (-686343270229075531845096560199204822651/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-884936672475634799279911414173430500000000000)
      constant := (9433284813025389081578992967544545308363019316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree041.table
  base := (-5491270097251680168441587226525174506489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-4976849281561611950324523532443535549000000000000)
      constant := (53110108862472294803479085412545849963332658475879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31577909802613838313/10000000000000000000)
  centralHi := (315779098026138383131/100000000000000000000)
  directionLo := (319701970151822104703/100000000000000000000)
  directionHi := (2497671641811110193/781250000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree042.table
  base := (-41080036340351407742182866480879531123/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17808400000000000000000000000000000000000000
      center := (178084)
      previous := (89042)
      next := (89042)
      square := (1639078479856540041109669297347200000000000)
      linear := (-72519461866904584364792659977528840000000000)
      constant := (792992744513225759025918043328286291974364585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree042.table
  base := (-2567728253866683436021130983671673905859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-2549041462544697184542187282240524394500000000000)
      constant := (27903731748635706723982419440056362840308639353949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319701970151822104703/100000000000000000000)
  centralHi := (2497671641811110193/781250000000000000)
  directionLo := (323577287039296980693/100000000000000000000)
  directionHi := (161788643519648490347/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree043.table
  base := (-2372941021302878186892081209236629587651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-928049874196979809839905085264790500000000000)
      constant := (10403617077247458336474703276601757514128189829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree043.table
  base := (-4746271702715541234063992973884539938529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-5219316568617176787844225596518562029000000000000)
      constant := (58572836215208357764380512913657575938537471848319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323577287039296980693/100000000000000000000)
  centralHi := (161788643519648490347/50000000000000000000)
  directionLo := (327406737341287202251/100000000000000000000)
  directionHi := (81851684335321800563/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree044.table
  base := (-4323631976222097591094684571716569808787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-1899212950115304630239803841620941000000000000)
      constant := (21813804973241919876753518055539130595542993973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree044.table
  base := (-86479354771017466218837746152380175499/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25011897800000000000000000000000000000000000000
      center := (250118978)
      previous := (125059489)
      next := (125059489)
      square := (2302085724958510487738530528124142400000000000)
      linear := (-106811004242899184132081532571121505380000000000)
      constant := (1228123909884889272633654637248252773938364739989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327406737341287202251/100000000000000000000)
  centralHi := (81851684335321800563/25000000000000000000)
  directionLo := (10349747252406361673/3125000000000000000)
  directionHi := (331191912077003573537/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree045.table
  base := (-3868467679161258023697125410608381815801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-1942326151836649640799797512712301000000000000)
      constant := (22844521571149912728606126564986349233178723679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree045.table
  base := (-483594606176072916771036162438770916029/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-2730891927836370812681963830296794254500000000000)
      constant := (32153757396241490014096300718467791323688405403276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10349747252406361673/3125000000000000000)
  centralHi := (331191912077003573537/100000000000000000000)
  directionLo := (13397372494275238497/4000000000000000000)
  directionHi := (167467156178440481213/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree046.table
  base := (-3380568818180771727416914948826816295201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-1985439353557994651359791183803661000000000000)
      constant := (23899375949275183054807828111906207311721356279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree046.table
  base := (-3380817738716371919356898161310080895927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-5583017499200524044123778692631101749000000000000)
      constant := (67276771761364556166476486992404991709106707198697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13397372494275238497/4000000000000000000)
  centralHi := (167467156178440481213/50000000000000000000)
  directionLo := (338635356338837928513/100000000000000000000)
  directionHi := (169317678169418964257/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree047.table
  base := (-2860086704695357083535671233038099693463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-2028552555279339661919784854895021000000000000)
      constant := (24978361371082236178305583779243077763547333777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree047.table
  base := (-572060175325734786527574723213602985509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 250118978000000000000000000000000000000000000000
      center := (2501189780)
      previous := (1250594890)
      next := (1250594890)
      square := (23020857249585104877385305281241424000000000000)
      linear := (-1140850228545661292576725944933722997800000000000)
      constant := (14062789516633713734218473469273588644633370055099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338635356338837928513/100000000000000000000)
  centralHi := (169317678169418964257/50000000000000000000)
  directionLo := (85574096376870516689/25000000000000000000)
  directionHi := (342296385507482066757/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree048.table
  base := (-2307148769839326989286736599073993612177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-2071665757000684672479778525986381000000000000)
      constant := (26081472163209541354601667932863394730392267783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree048.table
  base := (-2307332960557829644911333103875538704899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-5825484786256088881643480756706128229000000000000)
      constant := (73419026413181372645467352241726597421965609263389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85574096376870516689/25000000000000000000)
  centralHi := (342296385507482066757/100000000000000000000)
  directionLo := (345918670355102135409/100000000000000000000)
  directionHi := (34591867035510213541/10000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree049.table
  base := (-860931166636367524832171094431746996569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1057389479361014841519886098538870500000000000)
      constant := (13604351773839256668574066204048668691965751551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree049.table
  base := (-1722020670994447812609176290187374386667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-5946718429783871300403331788743641469000000000000)
      constant := (76591994909995326289223142843019915799701736566837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345918670355102135409/100000000000000000000)
  centralHi := (34591867035510213541/10000000000000000000)
  directionLo := (349503415532662362519/100000000000000000000)
  directionHi := (8737585388316559063/2500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree050.table
  base := (-276079444298234014396855243264236225801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1078946080221687346799882934084550500000000000)
      constant := (14180025750291671846604716695079290877982227358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree050.table
  base := (-1104453833952881827110274410944298361677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-6067952073311653719163182820781154709000000000000)
      constant := (79832841840014975660568480508084346426925137196947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349503415532662362519/100000000000000000000)
  centralHi := (8737585388316559063/2500000000000000000)
  directionLo := (353051764530007543511/100000000000000000000)
  directionHi := (44131470566250942939/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree051.table
  base := (-454591219422237827117454693419269407931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-2201005362164719704159759539260461000000000000)
      constant := (29535512633082465456595739650422011706689503949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree051.table
  base := (-227354041893961644099746025533930390871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-3094592858419718068961516926409333974500000000000)
      constant := (41570778872223279838666388780997701568281102475081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353051764530007543511/100000000000000000000)
  centralHi := (44131470566250942939/12500000000000000000)
  directionLo := (4457060049210320869/1250000000000000000)
  directionHi := (356564803936825669521/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree052.table
  base := (227253235372407854795629337035246316019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-2244118563886064714719753210351821000000000000)
      constant := (30735084091172001266800253474984918201235481899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree052.table
  base := (56788223670491877412109104713873372987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-3155209680183609278341442442428090594500000000000)
      constant := (43259067329449612318661117100478404251972921247286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4457060049210320869/1250000000000000000)
  centralHi := (356564803936825669521/100000000000000000000)
  directionLo := (180021783664687346863/50000000000000000000)
  directionHi := (360043567329374693727/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree053.table
  base := (11764519996854587877059820102045282239/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44521000000000000000000000000000000000000000
      center := (445210)
      previous := (222605)
      next := (222605)
      square := (4097696199641350102774173243368000000000000)
      linear := (-228723176560740972527974688144318100000000000)
      constant := (3195876347127701761737943361069022564084500152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree053.table
  base := (941075478280410317461364482294543914251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-2289659310749377349748214993554181000000000000)
      constant := (32026545346132407927992417588600227139606368771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180021783664687346863/50000000000000000000)
  centralHi := (360043567329374693727/100000000000000000000)
  directionLo := (363489038822379080249/100000000000000000000)
  directionHi := (1453956155289516321/400000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree054.table
  base := (42177210169329812384015492391465398479/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44521000000000000000000000000000000000000000
      center := (445210)
      previous := (222605)
      next := (222605)
      square := (4097696199641350102774173243368000000000000)
      linear := (-233034496732875473583974055253454100000000000)
      constant := (3320654874916421502638049578837335124022734236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree054.table
  base := (843507257921966592431670410995712912471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-3276443323711391697101293474465603834500000000000)
      constant := (46737422876512627908489164074316973147274324987319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363489038822379080249/100000000000000000000)
  centralHi := (1453956155289516321/400000000000000000)
  directionLo := (183451078160345002121/50000000000000000000)
  directionHi := (366902156320690004243/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree055.table
  base := (616248841326226678098843740365850824361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1186729084525049873199867111812950500000000000)
      constant := (17239219110036830755917343547375683589102752162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree055.table
  base := (2464931989735595697037755880652722937387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-6674120290950565812962437980968720909000000000000)
      constant := (97054969531650941723264702407776902418258197215243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183451078160345002121/50000000000000000000)
  centralHi := (366902156320690004243/100000000000000000000)
  directionLo := (92570953625289194261/25000000000000000000)
  directionHi := (74056762900231355409/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree056.table
  base := (3274850227496866063341371631335723992901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-2416571370771444756959727894717261000000000000)
      constant := (35774430448298976653228249298595233767887945421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree056.table
  base := (1637397944411934447096695403078819794349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-3397676967239174115861144506503117074500000000000)
      constant := (50351466604933620132544816203736756567204371027661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92570953625289194261/25000000000000000000)
  centralHi := (74056762900231355409/20000000000000000000)
  directionLo := (186817433775786915807/50000000000000000000)
  directionHi := (74726973510314766323/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree057.table
  base := (4116625835033854090213431102192362620903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-2459684572492789767519721565808621000000000000)
      constant := (37094524224724808698635224263317083176245222463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree057.table
  base := (4116579259517800469941314758902061100053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-6916587578006130650482140045043747389000000000000)
      constant := (104418733416871840231992747021666546898969406052917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186817433775786915807/50000000000000000000)
  centralHi := (74726973510314766323/20000000000000000000)
  directionLo := (75391226338092460449/20000000000000000000)
  directionHi := (188478065845231151123/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree058.table
  base := (4990299315891976928831830955346774833177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-2502797774214134778079715236899981000000000000)
      constant := (38438718531065781869328466567114571762347873217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree058.table
  base := (1247564851681925982558293913529349918167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-3518910610766956534620995538540630314500000000000)
      constant := (54101183657214211310929078898671379719286313673326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75391226338092460449/20000000000000000000)
  centralHi := (188478065845231151123/50000000000000000000)
  directionLo := (190124193744373440433/50000000000000000000)
  directionHi := (380248387488746880867/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree059.table
  base := (943336225258661542342149889331917229/1600000000000000000000000000000000000)
  polynomial :=
    { denominator := 8904200000000000000000000000000000000000000
      center := (89042)
      previous := (44521)
      next := (44521)
      square := (819539239928270020554834648673600000000000)
      linear := (-50918219518709595772794178159826820000000000)
      constant := (796140250194985703427978170182911065869038625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree059.table
  base := (5895817221064928109464290585494681630869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-7159054865061695488001842109118773869000000000000)
      constant := (112053832512726607617516088714232115629224163765941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190124193744373440433/50000000000000000000)
  centralHi := (380248387488746880867/100000000000000000000)
  directionLo := (76702476402407564847/20000000000000000000)
  directionHi := (95878095503009456059/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree060.table
  base := (6833265888861975068173210956846037140919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-2589024177656824799199702579082701000000000000)
      constant := (41199405438551389171077834750777802419550854799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree060.table
  base := (1708309153084108397491123717930650834051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-3640144254294738953380846570578143554500000000000)
      constant := (57986563499767537899017925703371987993987683719878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76702476402407564847/20000000000000000000)
  centralHi := (95878095503009456059/25000000000000000000)
  directionLo := (96687207700043711349/25000000000000000000)
  directionHi := (386748830800174845397/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree061.table
  base := (780252909709268146890550050870457215897/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44521000000000000000000000000000000000000000
      center := (445210)
      previous := (222605)
      next := (222605)
      square := (4097696199641350102774173243368000000000000)
      linear := (-263213737937816980975969625017406100000000000)
      constant := (4261589670923574978153747509459737725708950337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree061.table
  base := (195062600813521395698825512067850699557/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 125059489000000000000000000000000000000000000000
      center := (1250594890)
      previous := (625297445)
      next := (625297445)
      square := (11510428624792552438692652640620712000000000000)
      linear := (-740152215211726032552154417319380034900000000000)
      constant := (11996024908054769954226950489700810656034563785492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96687207700043711349/25000000000000000000)
  centralHi := (386748830800174845397/100000000000000000000)
  directionLo := (194979209849446069729/50000000000000000000)
  directionHi := (389958419698892139459/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree062.table
  base := (1760725905401616328469691686704023596923/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 89042000000000000000000000000000000000000000
      center := (890420)
      previous := (445210)
      next := (445210)
      square := (8195392399282700205548346486736000000000000)
      linear := (-535050116219902964063937984253084200000000000)
      constant := (8811297161912749105156895124792946234558608883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree062.table
  base := (2200902018556469029829235874020945785069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-3761377897822521372140697602615656794500000000000)
      constant := (62007598664577160540607772360497571010604865939482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194979209849446069729/50000000000000000000)
  centralHi := (389958419698892139459/100000000000000000000)
  directionLo := (393141806556886476911/100000000000000000000)
  directionHi := (24571362909805404807/6250000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree063.table
  base := (9836557488988037733167581548749631256211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-2718363782820859830879683592356781000000000000)
      constant := (45521172308143798246361488922689865333157769931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree063.table
  base := (4918269566150349534823825533021967487503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-3821994719586412581520623118634413414500000000000)
      constant := (64068985272073596872122838149506003781386739065967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393141806556886476911/100000000000000000000)
  centralHi := (24571362909805404807/6250000000000000000)
  directionLo := (99074905700045768673/25000000000000000000)
  directionHi := (396299622800183074693/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree064.table
  base := (5450652411373056825835329437334437251783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1380738492271102420719838631724070500000000000)
      constant := (23504977920835897761059664032872238480886630943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree064.table
  base := (10901289119278471660800746418122474975049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-7765223082700607581801097269306340069000000000000)
      constant := (132328567714109344398692653642229985555794915689961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99074905700045768673/25000000000000000000)
  centralHi := (396299622800183074693/100000000000000000000)
  directionLo := (7988649497889425429/2000000000000000000)
  directionHi := (399432474894471271451/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree065.table
  base := (11997864655963900192237517095049135054697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-2804590186263549851999670934539501000000000000)
      constant := (48522836104185249456814577316916747541770165137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree065.table
  base := (5998925612753667331573233476571088803593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-3943228363114195000280474150671926654500000000000)
      constant := (68293493993714595630699522490402330177325961943977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7988649497889425429/2000000000000000000)
  centralHi := (399432474894471271451/100000000000000000000)
  directionLo := (201270472852501057321/50000000000000000000)
  directionHi := (402540945705002114643/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree066.table
  base := (13126231201018082192276031622058964631663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-2847703387984894862559664605630861000000000000)
      constant := (50059812838013382436093472697431833164366268423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree066.table
  base := (6563109858641211460965487115022999129269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-4003845184878086209660399666690683274500000000000)
      constant := (70456615323526266909648714679254440670103826083541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201270472852501057321/50000000000000000000)
  centralHi := (402540945705002114643/100000000000000000000)
  directionLo := (50703199470335526207/12500000000000000000)
  directionHi := (405625595762684209657/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree067.table
  base := (446449986993388113773543636542621391157/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1445408294853119936559829138361110500000000000)
      constant := (25810442913077743627212411323760018251291212752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree067.table
  base := (1785798720856757522989637515347124816293/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-4064462006641977419040325182709439894500000000000)
      constant := (72653647544611732270121265966845440105704285817108) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50703199470335526207/12500000000000000000)
  centralHi := (405625595762684209657/100000000000000000000)
  directionLo := (408686964444166650633/100000000000000000000)
  directionHi := (204343482222083325317/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree068.table
  base := (7739182849741801975097772933128111464577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1466964895713792441839825973906790500000000000)
      constant := (26603027442931075031092847149179990650514432617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree068.table
  base := (15478357309292914102965216620663500461519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-8250157656811737256840501397456393029000000000000)
      constant := (149769180805583998299914959704685970375668830303791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408686964444166650633/100000000000000000000)
  centralHi := (204343482222083325317/50000000000000000000)
  directionLo := (82345114214588973139/20000000000000000000)
  directionHi := (12866424096029527053/3125000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree069.table
  base := (1670212609122100178012579103512473901719/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44521000000000000000000000000000000000000000
      center := (445210)
      previous := (222605)
      next := (222605)
      square := (4097696199641350102774173243368000000000000)
      linear := (-297704299314892989423964561890494100000000000)
      constant := (5481531986322949914042472497552733750578431599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree069.table
  base := (417552973049225408469377598916207511787/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 125059489000000000000000000000000000000000000000
      center := (1250594890)
      previous := (625297445)
      next := (625297445)
      square := (11510428624792552438692652640620712000000000000)
      linear := (-837139130033951967560035242949390626900000000000)
      constant := (15429888736810178022159058908083827891943174787372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82345114214588973139/20000000000000000000)
  centralHi := (12866424096029527053/3125000000000000000)
  directionLo := (207370957973927494113/50000000000000000000)
  directionHi := (414741915947854988227/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree070.table
  base := (8978838923884621762610557885666040056259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1510078097435137452399819644998150500000000000)
      constant := (28224340314323301341471664339513772769344706939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree070.table
  base := (8978835861535955779759194544046784630057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-4246312471933651047180101730765709754500000000000)
      constant := (79448207208189533683306819146867071849177982460873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207370957973927494113/50000000000000000000)
  centralHi := (414741915947854988227/100000000000000000000)
  directionLo := (208868240652362374461/50000000000000000000)
  directionHi := (417736481304724748923/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree071.table
  base := (4811254629357338497264459996651975310617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1531634698295809957679816480543830500000000000)
      constant := (29053068536480685307510763373825360685607958914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree071.table
  base := (19245013286163649436410159966407040832511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-8613858587395084513120054493568932749000000000000)
      constant := (163561761646966769576658884251666672757765960246879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208868240652362374461/50000000000000000000)
  centralHi := (417736481304724748923/100000000000000000000)
  directionLo := (420709732216415083399/100000000000000000000)
  directionHi := (2103548661082075417/500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree072.table
  base := (20564146035507420031486913291979719592459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-3106382598312964925919626632179021000000000000)
      constant := (59787689104251565229746743309029421095975867139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree072.table
  base := (20564141568231607643858334583439327719013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-8735092230922866931879905525606445989000000000000)
      constant := (168294928804366772283137789556250609865043301364357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420709732216415083399/100000000000000000000)
  centralHi := (2103548661082075417/500000000000000000)
  directionLo := (211831058718004526107/50000000000000000000)
  directionHi := (84732423487201810443/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree073.table
  base := (21915058663233760032851611362520333248307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-3149495800034309936479620303270381000000000000)
      constant := (61493336645105421531730241339493560756547875947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree073.table
  base := (21915054849108320228407448047175445688811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-8856325874450649350639756557643959229000000000000)
      constant := (173095915673455811199486315983833120911939956677579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211831058718004526107/50000000000000000000)
  centralHi := (84732423487201810443/20000000000000000000)
  directionLo := (426594070187476660413/100000000000000000000)
  directionHi := (213297035093738330207/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree074.table
  base := (23297754936322091013877403311776519832541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-3192609001755654947039613974361741000000000000)
      constant := (63223079630331449916451739449447356439464557861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree074.table
  base := (11648875840231223703010208093261468388637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-4488779758989215884699803794840736234500000000000)
      constant := (88982361036553154534813707715463697266822596626493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426594070187476660413/100000000000000000000)
  centralHi := (213297035093738330207/50000000000000000000)
  directionLo := (214753004453879993371/50000000000000000000)
  directionHi := (429506008907759986743/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree075.table
  base := (6178058405411823287492991577560285124883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1617861101738499978799803822726550500000000000)
      constant := (32488459002514843462100281417099160408089832086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree075.table
  base := (12356115421424374308611208905162509059483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-4549396580753107094079729310859492854500000000000)
      constant := (91450673925407533622855546325500496073061814584187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214753004453879993371/50000000000000000000)
  centralHi := (429506008907759986743/100000000000000000000)
  directionLo := (216199168971938834631/50000000000000000000)
  directionHi := (432398337943877669263/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree076.table
  base := (6539623420190120024516903233043021334407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1639417702599172484079800658272230500000000000)
      constant := (33377425861483674843048497490932494705658268094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree076.table
  base := (26158491309543821144000957334553457859173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-9220026805033996606919309653756498949000000000000)
      constant := (187905792878180581639481493850700586512051209342597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216199168971938834631/50000000000000000000)
  centralHi := (432398337943877669263/100000000000000000000)
  directionLo := (435271448208336859187/100000000000000000000)
  directionHi := (108817862052084214797/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree077.table
  base := (13818267119581149084531859149672085936717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1660974303459844989359797493817910500000000000)
      constant := (34278440372605426238274293486121949437988577557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree077.table
  base := (27636532216095523625323025638053425481529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-9341260448561779025679160685794012189000000000000)
      constant := (192978057047094909187372066397202215437169595678681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435271448208336859187/100000000000000000000)
  centralHi := (108817862052084214797/25000000000000000000)
  directionLo := (438125717795860409403/100000000000000000000)
  directionHi := (109531429448965102351/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree078.table
  base := (29146354560425678380325286985052719274627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-3365061808641034989279588658727181000000000000)
      constant := (70383005038973725757379446173942730114825668667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree078.table
  base := (29146352834683380407626739725357101984497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-9462494092089561444439011717831525429000000000000)
      constant := (198118140266537193120411420173214884161202080742033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438125717795860409403/100000000000000000000)
  centralHi := (109531429448965102351/25000000000000000000)
  directionLo := (440961512564183941943/100000000000000000000)
  directionHi := (55120189070522992743/12500000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree079.table
  base := (30687954024402689426064259268778652855733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-3408175010362379999839582329818541000000000000)
      constant := (72233224576646363478924582380144253403790088893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree079.table
  base := (1917997034533117484888756850052727699033/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-4791863867808671931599431374934519334500000000000)
      constant := (101663021229936895475308795157746568836402702193096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440961512564183941943/100000000000000000000)
  centralHi := (55120189070522992743/12500000000000000000)
  directionLo := (221889593340724290907/50000000000000000000)
  directionHi := (88755837336289716363/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree080.table
  base := (16130666054435464172469312715324029764433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1725644106041862505199788000454950500000000000)
      constant := (37053769667489451019471043988054981129142321593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree080.table
  base := (16130665426861332116868792563152840450107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-4852480689572563140979356890953275954500000000000)
      constant := (104300881781292483443668967341774441565588911415323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221889593340724290907/50000000000000000000)
  centralHi := (88755837336289716363/20000000000000000000)
  directionLo := (4465790831425079499/1000000000000000000)
  directionHi := (446579083142507949901/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree081.table
  base := (169332441870383057242782730994037179459/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8904200000000000000000000000000000000000000
      center := (89042)
      previous := (44521)
      next := (44521)
      square := (819539239928270020554834648673600000000000)
      linear := (-69888028276101400419191393440025220000000000)
      constant := (1520118985887861264676821397712353337066776556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree081.table
  base := (16933243651954362345592061811023987185549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-4913097511336454350359282406972032574500000000000)
      constant := (106972651760175377780768582655163121525542306124461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4465790831425079499/1000000000000000000)
  centralHi := (446579083142507949901/100000000000000000000)
  directionLo := (224680767128140090191/50000000000000000000)
  directionHi := (449361534256280180383/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree082.table
  base := (887585561242929985617823257753673768561/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44521000000000000000000000000000000000000000
      center := (445210)
      previous := (222605)
      next := (222605)
      square := (4097696199641350102774173243368000000000000)
      linear := (-353751461552641503151956334309262100000000000)
      constant := (7792845443840260771090284524054245439400417124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree082.table
  base := (35503421537406847915580744799921456273617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-9947428666200691119478415845981578389000000000000)
      constant := (219356662287439251311649963775248222317214386201713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224680767128140090191/50000000000000000000)
  centralHi := (449361534256280180383/100000000000000000000)
  directionLo := (226063431053052620819/50000000000000000000)
  directionHi := (452126862106105241639/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree083.table
  base := (37172134023978541162367720195613835160507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-3580627817247760042079557014183981000000000000)
      constant := (79875054753125257648512799637852526555180932147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree083.table
  base := (1486885329854250217170218303162025194627/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50023795600000000000000000000000000000000000000
      center := (500237956)
      previous := (250118978)
      next := (250118978)
      square := (4604171449917020975477061056248284800000000000)
      linear := (-402746492389138941529530675120763665160000000000)
      constant := (8993433593013981699924658918565118945375178165603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226063431053052620819/50000000000000000000)
  centralHi := (452126862106105241639/100000000000000000000)
  directionLo := (28429711186557056347/6250000000000000000)
  directionHi := (454875378984912901553/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree084.table
  base := (38872622834302284607031457109146580328629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-3623741018969105052639550685275341000000000000)
      constant := (81845750226871652654853007884714478902810891709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree084.table
  base := (19436311085789866412439729576830773444607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-5094947976628127978499058955028302434500000000000)
      constant := (115191418050834529563356357471546820391957321225823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28429711186557056347/6250000000000000000)
  centralHi := (454875378984912901553/100000000000000000000)
  directionLo := (457607387806865700741/100000000000000000000)
  directionHi := (228803693903432850371/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree085.table
  base := (20302444329805238463388080965609581412669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1833427110345225031599772178183350500000000000)
      constant := (41920270424899590595946602211373946674073436549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree085.table
  base := (20302444047445187135860559326910844737981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-5155564798392019187878984471047059054500000000000)
      constant := (117998825544555729123878135729707418808365242751709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457607387806865700741/100000000000000000000)
  centralHi := (228803693903432850371/50000000000000000000)
  directionLo := (230161591248506435859/50000000000000000000)
  directionHi := (460323182497012871719/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree086.table
  base := (42368931313757373916083495648751683164607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-3709967422411795073759538027458061000000000000)
      constant := (85859426613620448581859507280751439686171468247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree086.table
  base := (42368930832613862331753954038562475489699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-10432363240311820794517819974131631349000000000000)
      constant := (241680284764706523580023761500580356185816781703811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230161591248506435859/50000000000000000000)
  centralHi := (460323182497012871719/100000000000000000000)
  directionLo := (231511524180187008303/50000000000000000000)
  directionHi := (463023048360374016607/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree087.table
  base := (44164750640014774497142419103930078904897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-3753080624133140084319531698549421000000000000)
      constant := (87902407511357758584566691184380078042924919337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree087.table
  base := (22082375115067118753100299699073349152553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-5276798441919801606638835503084572294500000000000)
      constant := (123715368554559031118676695780576220653161861225417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231511524180187008303/50000000000000000000)
  centralHi := (463023048360374016607/100000000000000000000)
  directionLo := (116426815607941104259/25000000000000000000)
  directionHi := (465707262431764417037/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree088.table
  base := (45992346506427763846624190989385778904377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-3796193825854485094879525369640781000000000000)
      constant := (89969483537136346437165337241888452262601768417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree088.table
  base := (22996173078650726602281842850180007520003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-5337415263683692816018761019103328914500000000000)
      constant := (126624504053034787949905684207058971359467732458467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116426815607941104259/25000000000000000000)
  centralHi := (465707262431764417037/100000000000000000000)
  directionLo := (58547011725947013077/12500000000000000000)
  directionHi := (468376093807576104617/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree089.table
  base := (47851718801903492118651571831030239535883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-3839307027575830105439519040732141000000000000)
      constant := (92060654686010247371667144874650666294377047043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree089.table
  base := (5981464813070569939573567808851037555093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-5398032085447584025398686535122085534500000000000)
      constant := (129567548870930339376078323555042871767413959709908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58547011725947013077/12500000000000000000)
  centralHi := (468376093807576104617/100000000000000000000)
  directionLo := (471029803960639383303/100000000000000000000)
  directionHi := (58878725495079922913/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree090.table
  base := (3108929214557331019639932308426136074671/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1941210114648587557999756355911750500000000000)
      constant := (47087960476907824933347137097621565033443420728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree090.table
  base := (49742867179715870603227733275837996996457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-10917297814422950469557224102281684309000000000000)
      constant := (265089006004959924721485419001903147448660447230473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471029803960639383303/100000000000000000000)
  centralHi := (58878725495079922913/12500000000000000000)
  directionLo := (94733729407841514939/20000000000000000000)
  directionHi := (59208580879900946837/12500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree091.table
  base := (51665792320738731767951029382586733186353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-3925533431018520126559506382914861000000000000)
      constant := (96315282337047395795296884801672314948189621913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree091.table
  base := (25832896052574791693339783406957973717473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-5519265728975366444158537567159598774500000000000)
      constant := (135555366442830985865726588666032336447707603751297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94733729407841514939/20000000000000000000)
  centralHi := (59208580879900946837/12500000000000000000)
  directionLo := (238146435075516322839/50000000000000000000)
  directionHi := (476292870151032645679/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree092.table
  base := (3351280837443466062052944711764277552149/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-1984323316369932568559750027003110500000000000)
      constant := (49239369416377487121067442806893465207193805032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree092.table
  base := (53620493215553566447057942999919695913799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-11159765101478515307076926166356710789000000000000)
      constant := (277200278375798918001188121985722049045015090988711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238146435075516322839/50000000000000000000)
  centralHi := (476292870151032645679/100000000000000000000)
  directionLo := (239451356816715220311/50000000000000000000)
  directionHi := (478902713633430440623/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree093.table
  base := (27803485306102933014705586838847099098321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2005879917230605073839746862548790500000000000)
      constant := (50333145219227466164142332369432518198956349241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree093.table
  base := (11121394091193175945988756678296715136829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 250118978000000000000000000000000000000000000000
      center := (2501189780)
      previous := (1250594890)
      next := (1250594890)
      square := (23020857249585104877385305281241424000000000000)
      linear := (-2256199749001259545167355439678844805800000000000)
      constant := (56671528493699450278607194164204421932540399820381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239451356816715220311/50000000000000000000)
  centralHi := (478902713633430440623/100000000000000000000)
  directionLo := (481498411310170908517/100000000000000000000)
  directionHi := (240749205655085454259/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree094.table
  base := (57625223913122268993273856589175995071053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-4054873036182555158239487396188941000000000000)
      constant := (102877937152057111952404214449655278476558350613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree094.table
  base := (28812611890069199256666166932610903595251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-5701116194267040072298314115215868634500000000000)
      constant := (144791412578986602531027271115861793103700352886739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481498411310170908517/100000000000000000000)
  centralHi := (240749205655085454259/50000000000000000000)
  directionLo := (96816038147194095587/20000000000000000000)
  directionHi := (30255011920998154871/6250000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree095.table
  base := (14918813315583901693345861423576803778567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2048993118951950084399740533640150500000000000)
      constant := (52556839485901265146905200595004173262051162814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree095.table
  base := (59675253149159019609992630636430874478191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-11523466032061862563356479262469250509000000000000)
      constant := (295875826439360451267733460561933950957315708104399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96816038147194095587/20000000000000000000)
  centralHi := (30255011920998154871/6250000000000000000)
  directionLo := (486648273429310130107/100000000000000000000)
  directionHi := (121662068357327532527/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree096.table
  base := (61757058626600421453038822756627878396539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-4141099439625245179359474738371661000000000000)
      constant := (107373515896211066320593774474918805774092312819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree096.table
  base := (30878529265145796943395054613553411592953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-5822349837794822491058165147253381874500000000000)
      constant := (151118323154282511963827562104898238820021378181017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486648273429310130107/100000000000000000000)
  centralHi := (121662068357327532527/25000000000000000000)
  directionLo := (489202875094253338989/100000000000000000000)
  directionHi := (48920287509425333899/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree097.table
  base := (63870639977945318794063677738992011122477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-4184212641346590189919468409463021000000000000)
      constant := (109657447924037405589876486805222880327183798517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree097.table
  base := (12774127979199836824133018330562520609429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 250118978000000000000000000000000000000000000000
      center := (2501189780)
      previous := (1250594890)
      next := (1250594890)
      square := (23020857249585104877385305281241424000000000000)
      linear := (-2353186663823485480175236265308855397800000000000)
      constant := (61733056952428633548815722166014583759317159321781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489202875094253338989/100000000000000000000)
  centralHi := (48920287509425333899/10000000000000000000)
  directionLo := (49174420583189251411/10000000000000000000)
  directionHi := (491744205831892514111/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree098.table
  base := (33007998646419822857933397709005676800617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2113662921533967600239731040277190500000000000)
      constant := (55982737527116969947928768343980050736840269457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree098.table
  base := (33007998611560841166354174958392358786583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-5943583481322604909818016179290895114500000000000)
      constant := (157580870898599245723988354796051768951104730036087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49174420583189251411/10000000000000000000)
  centralHi := (491744205831892514111/100000000000000000000)
  directionLo := (123568117585502640229/25000000000000000000)
  directionHi := (494272470342010560917/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree099.table
  base := (34096565275745863192171807121925227585961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2135219522394640105519727875822870500000000000)
      constant := (57148798642959762019363377469185122557354569681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree099.table
  base := (68193130492183397166892199902937935992117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-12008400606172992238395883390619303469000000000000)
      constant := (321726017411295375030442881250477299316138860048213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123568117585502640229/25000000000000000000)
  centralHi := (494272470342010560917/100000000000000000000)
  directionLo := (31049241757219085019/6250000000000000000)
  directionHi := (99357573623101072061/20000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree100.table
  base := (17600509934314472989847643046045004513593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2156776123255312610799724711368550500000000000)
      constant := (58326907309176582619026945435605989291899347906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree100.table
  base := (8800254960851259409150318295816744824067/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-6064817124850387328577867211328408354500000000000)
      constant := (164179055801193031367383912455544950668864855687052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31049241757219085019/6250000000000000000)
  centralHi := (99357573623101072061/20000000000000000000)
  directionLo := (499290593618089089313/100000000000000000000)
  directionHi := (249645296809044544657/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree101.table
  base := (283760643891190688771376993692077584663/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2178332724115985116079721546914230500000000000)
      constant := (59517063525455933310924601839577008726788022144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree101.table
  base := (72642724793238065247411768663821064404821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-12250867893228557075915585454694329949000000000000)
      constant := (335058024368749279349564701896547902699653003396469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499290593618089089313/100000000000000000000)
  centralHi := (249645296809044544657/50000000000000000000)
  directionLo := (31361302279108819363/6250000000000000000)
  directionHi := (501780836465741109809/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree102.table
  base := (74915185836390430174648424857100349225621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-4399778649953315242719436764919821000000000000)
      constant := (121438534583071969102453851923569786647873872541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree102.table
  base := (37457592899950532327771489977091058722107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-6186050768378169747337718243365921594500000000000)
      constant := (170912877854469274501410453250376449965505694423323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31361302279108819363/6250000000000000000)
  centralHi := (501780836465741109809/100000000000000000000)
  directionLo := (504258781592362415991/100000000000000000000)
  directionHi := (63032347699045301999/12500000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree103.table
  base := (77219422728111010255984666351233960190371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-4442891851674660253279430436011181000000000000)
      constant := (123867037214393439437013018606256510141635507291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree103.table
  base := (77219422697082191018232208072041331566783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-12493335180284121913435287518769356429000000000000)
      constant := (348661305621738683336994127319667761825871451353887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504258781592362415991/100000000000000000000)
  centralHi := (63032347699045301999/12500000000000000000)
  directionLo := (506724609410051150319/100000000000000000000)
  directionHi := (6334057617625639379/1250000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree104.table
  base := (9944429437875499774582332451656872813887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2243002526698002631919712053551270500000000000)
      constant := (63159817472253319712105134927158354538188252508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree104.table
  base := (79555435476621054541532511714811566197273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-12614568823811904332195138550806869669000000000000)
      constant := (355564674106129148174412544580877946205920634573497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506724609410051150319/100000000000000000000)
  centralHi := (6334057617625639379/1250000000000000000)
  directionLo := (509178495962392285171/100000000000000000000)
  directionHi := (127294623990598071293/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree105.table
  base := (8192322415409775193579921150583107434889/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 44521000000000000000000000000000000000000000
      center := (445210)
      previous := (222605)
      next := (222605)
      square := (4097696199641350102774173243368000000000000)
      linear := (-452911825511735027439941777819390100000000000)
      constant := (12879632777310118458785355927808321026108693169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree105.table
  base := (81923224131667141275356788847233335470637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-12735802467339686750954989582844382909000000000000)
      constant := (362535861161253221741090893798363041786473437724493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509178495962392285171/100000000000000000000)
  centralHi := (127294623990598071293/25000000000000000000)
  directionLo := (511620613071130055797/100000000000000000000)
  directionHi := (255810306535565027899/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree106.table
  base := (42161394337770410626143103428858505825579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2286115728419347642479705724642630500000000000)
      constant := (65648557849958281256324199115008502537860602659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree106.table
  base := (84322788656472188606274977342581438550893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-4577086547122630533896347673507261000000000000)
      constant := (131568126303450348612301818036780541725724307253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511620613071130055797/100000000000000000000)
  centralHi := (255810306535565027899/50000000000000000000)
  directionLo := (514051128476568965071/100000000000000000000)
  directionHi := (32128195529785560317/6250000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree107.table
  base := (43377064531212254088516559805102698962117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2307672329280020147759702560188310500000000000)
      constant := (66910999362367116528156542741729190760492410957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree107.table
  base := (86754129046215391256939352104470212487679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-12978269754395251588474691646919409389000000000000)
      constant := (376681690980942683262453674005871979213680554536031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514051128476568965071/100000000000000000000)
  centralHi := (32128195529785560317/6250000000000000000)
  directionLo := (258235102986014011333/50000000000000000000)
  directionHi := (516470205972028022667/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree108.table
  base := (89217245310633457842505756661090700951667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-4658457860281385306079398791467981000000000000)
      constant := (136370976847370976504790131227304047097069166507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree108.table
  base := (89217245296856249547578851600510996668499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-13099503397923034007234542678956922629000000000000)
      constant := (383856333744399880947327662627801271459243187337011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258235102986014011333/50000000000000000000)
  centralHi := (516470205972028022667/100000000000000000000)
  directionLo := (259439002766326601557/50000000000000000000)
  directionHi := (103775601106530640623/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree109.table
  base := (45856068708359927331564674025594597050753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2350785531001365158319696231279670500000000000)
      constant := (69472025033836646330197080564100591555296574313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree109.table
  base := (45856068702505345718933284554383590430449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-6610368520725408212997196855497217934500000000000)
      constant := (195549397538170205993237651191754180439092241980561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259439002766326601557/50000000000000000000)
  centralHi := (103775601106530640623/20000000000000000000)
  directionLo := (104254936687774958509/20000000000000000000)
  directionHi := (260637341719437396273/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree110.table
  base := (94238805377797497188873448309256298814681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-4744684263724075327199386133650701000000000000)
      constant := (141541218385512684948368369723324509679528412801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree110.table
  base := (94238805367846790112211382405458666541033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-13341970684978598844754244743031949109000000000000)
      constant := (398409074976410117059453370294750764700742984512137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104254936687774958509/20000000000000000000)
  centralHi := (260637341719437396273/50000000000000000000)
  directionLo := (261830196197389618313/50000000000000000000)
  directionHi := (523660392394779236627/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree111.table
  base := (96797249191452613188531311728099200191847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-4787797465445420337759379804742061000000000000)
      constant := (144162481800781689815207201487044095491741220287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree111.table
  base := (96797249182996980060855851007567221999219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-13463204328506381263514095775069462349000000000000)
      constant := (405787173444312909633437576340774309691621886539091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261830196197389618313/50000000000000000000)
  centralHi := (523660392394779236627/100000000000000000000)
  directionLo := (526035281641649205471/100000000000000000000)
  directionHi := (16438602551301537671/3125000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree112.table
  base := (3105858401739649121769359387632653956423/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2415455333583382674159686737916710500000000000)
      constant := (73403920156695266873400284140229710188702534128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree112.table
  base := (99387468848484163972887154542901942378003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-13584437972034163682273946807106975589000000000000)
      constant := (413233090479801534929021889082284011478900500020467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526035281641649205471/100000000000000000000)
  centralHi := (16438602551301537671/3125000000000000000)
  directionLo := (33024968566681922891/6250000000000000000)
  directionHi := (528399497066910766257/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree113.table
  base := (51004732184381833775142476281474126009523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2437011934444055179439683573462390500000000000)
      constant := (74738646961632159404140244470148526064069973483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree113.table
  base := (102009464362659514803064105277731994032749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-13705671615561946101033797839144488829000000000000)
      constant := (420746826082669791478479065699546423943436639205261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33024968566681922891/6250000000000000000)
  centralHi := (528399497066910766257/100000000000000000000)
  directionLo := (530753181308712719923/100000000000000000000)
  directionHi := (132688295327178179981/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree114.table
  base := (20932647145867179937920467147769231949501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 89042000000000000000000000000000000000000000
      center := (890420)
      previous := (445210)
      next := (445210)
      square := (8195392399282700205548346486736000000000000)
      linear := (-983427414121891073887872163603228200000000000)
      constant := (30434168526068130649954125547973312775623734021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree114.table
  base := (104663235724150124317844442505980806669969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-13826905259089728519793648871182002069000000000000)
      constant := (428328380252745984079678418408754832009454114785841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530753181308712719923/100000000000000000000)
  centralHi := (132688295327178179981/25000000000000000000)
  directionLo := (266548236928175120117/50000000000000000000)
  directionHi := (106619294771270048047/20000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree115.table
  base := (107348782936220171588211334161625342510483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-4960250272330800379999354489107501000000000000)
      constant := (154888486434567656895716697060757836873909213643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree115.table
  base := (26837195732953735388208009480178677254463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-6974069451308755469276749951609757654500000000000)
      constant := (217988876494943706741044805105132837795403131498814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266548236928175120117/50000000000000000000)
  centralHi := (106619294771270048047/20000000000000000000)
  directionLo := (267714755573366441697/50000000000000000000)
  directionHi := (107085902229346576679/20000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree116.table
  base := (110066105988449577373322191934111187018583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-5003363474052145390559348160198861000000000000)
      constant := (157630225335902282129756224180672760157254333743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree116.table
  base := (110066105984707690584688485269248423235631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-14069372546145293357313350935257028549000000000000)
      constant := (443694944293975738902286936844043728962903739452559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267714755573366441697/50000000000000000000)
  centralHi := (107085902229346576679/20000000000000000000)
  directionLo := (537752426657085751993/100000000000000000000)
  directionHi := (268876213328542875997/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree117.table
  base := (112815204885223858255394849244497116974031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-5046476675773490401119341831290221000000000000)
      constant := (160396059334308900630320096096729893144800834151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree117.table
  base := (112815204882045664127706525971337718869789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-14190606189673075776073201967294541789000000000000)
      constant := (451479954164913075367083271548452783170031469877821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537752426657085751993/100000000000000000000)
  centralHi := (268876213328542875997/50000000000000000000)
  directionLo := (540065350994062040589/100000000000000000000)
  directionHi := (54006535099406204059/10000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree118.table
  base := (57798039812941342512848154557480295006383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2544794938747417705839667751190790500000000000)
      constant := (81592994214879056940353155525239799213979177543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree118.table
  base := (115596079623183463848942137063408460938831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-14311839833200858194833052999332055029000000000000)
      constant := (459332782602618709690759182946063991277786665117359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540065350994062040589/100000000000000000000)
  centralHi := (54006535099406204059/10000000000000000000)
  directionLo := (542368411979435309173/100000000000000000000)
  directionHi := (271184205989717654587/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree119.table
  base := (118408730209883172822211776339806771527597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-5132703079216180422239329173472941000000000000)
      constant := (166000012622225752103973108344569136275180146037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree119.table
  base := (592043651037954525630841776449978727509/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25011897800000000000000000000000000000000000000
      center := (250118978)
      previous := (125059489)
      next := (125059489)
      square := (2302085724958510487738530528124142400000000000)
      linear := (-288661469534572812271858080627391365380000000000)
      constant := (9345068592140526745107666179402542718837583131604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542368411979435309173/100000000000000000000)
  centralHi := (271184205989717654587/50000000000000000000)
  directionLo := (544661734732530576401/100000000000000000000)
  directionHi := (272330867366265288201/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree120.table
  base := (60626578318390479756858141295445124091239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2587908140468762716399661422282150500000000000)
      constant := (84419065955846015926838110582030572369666051519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree120.table
  base := (121253156634834427603234931049994540448071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-14554307120256423032352755063407081509000000000000)
      constant := (475241895178081737224364841398305568011225590295719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544661734732530576401/100000000000000000000)
  centralHi := (272330867366265288201/50000000000000000000)
  directionLo := (68368180218693081529/12500000000000000000)
  directionHi := (546945441749544652233/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree121.table
  base := (62064679453107142308022752586965006797463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2609464741329435221679658257827830500000000000)
      constant := (85850173149070423595650084849141769567629850223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree121.table
  base := (62064679452280728496599984869744617741909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-7337770381892102725556303047722297374500000000000)
      constant := (241649089657870408418772143759370871931678473424501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68368180218693081529/12500000000000000000)
  centralHi := (546945441749544652233/100000000000000000000)
  directionLo := (109843930595979599649/20000000000000000000)
  directionHi := (274609826489948999123/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree122.table
  base := (127037337017890594556392081738270574345249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-5262042684380215453919310186747021000000000000)
      constant := (174586655781559173339229997368022786240424830729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree122.table
  base := (6351866850824362561361494874112142584957/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 125059489000000000000000000000000000000000000000
      center := (1250594890)
      previous := (625297445)
      next := (625297445)
      square := (11510428624792552438692652640620712000000000000)
      linear := (-1479677440731198786987245712748210798900000000000)
      constant := (49142228201996796639729651775642971767289723013946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109843930595979599649/20000000000000000000)
  centralHi := (274609826489948999123/50000000000000000000)
  directionLo := (882375177439604441/160000000000000000)
  directionHi := (275742242949876387813/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree123.table
  base := (1015446023215431835707977740945834617761/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2652577943050780232239651928919190500000000000)
      constant := (88748530180968282515680028003490989693109598784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree123.table
  base := (64988545485191918922752577777169869546031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-7459004025419885144316154079759810614500000000000)
      constant := (249807101645367337892145212532575553085748298838159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (882375177439604441/160000000000000000)
  centralHi := (275742242949876387813/50000000000000000000)
  directionLo := (553740055582824580487/100000000000000000000)
  directionHi := (69217506947853072561/12500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree124.table
  base := (16618577595885271721239934560712287131653/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2674134543911452737519648764464870500000000000)
      constant := (90215780019632367295272145767677788941553292852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree124.table
  base := (33237155191517677915849813091467495079189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 625297445000000000000000000000000000000000000000
      center := (6252974450)
      previous := (3126487225)
      next := (3126487225)
      square := (57552143123962762193463263203103560000000000000)
      linear := (-7519620847183776353696079595778567234500000000000)
      constant := (253936971564009185556187384875404488769926781748842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553740055582824580487/100000000000000000000)
  centralHi := (69217506947853072561/12500000000000000000)
  directionLo := (277993237384304320823/50000000000000000000)
  directionHi := (555986474768608641647/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree125.table
  base := (135951926404265631811793135220581837397289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-5391382289544250485599291200021101000000000000)
      constant := (183390154813537197126099731987155648982764703569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree125.table
  base := (135951926403407014064480200940419938617697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-15160475337895335126152010223594647709000000000000)
      constant := (516201501531801436674957320518878387312690553176833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277993237384304320823/50000000000000000000)
  centralHi := (555986474768608641647/100000000000000000000)
  directionLo := (4465790831425079499/800000000000000000)
  directionHi := (17444495435254216793/3125000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree126.table
  base := (138987007883013782727355997280170034687869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-5434495491265595496159284871112461000000000000)
      constant := (186372844684748972235417197979090256114338615749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree126.table
  base := (138987007882284959322781599501304104966533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-15281708981423117544911861255632160949000000000000)
      constant := (524596878502070392844227225131998353617216979081637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4465790831425079499/800000000000000000)
  centralHi := (17444495435254216793/3125000000000000000)
  directionLo := (560452301327360747421/100000000000000000000)
  directionHi := (280226150663680373711/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree127.table
  base := (71026932601621460557465746258854070247053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2738804346493470253359639271101910500000000000)
      constant := (94689814826448166635154323465827865561469046613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree127.table
  base := (28410773040524862089313082998188708398623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 250118978000000000000000000000000000000000000000
      center := (2501189780)
      previous := (1250594890)
      next := (1250594890)
      square := (23020857249585104877385305281241424000000000000)
      linear := (-3080588524990179992734342457533934837800000000000)
      constant := (106612014807763041044599765590824589393751800683647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560452301327360747421/100000000000000000000)
  centralHi := (280226150663680373711/50000000000000000000)
  directionLo := (562671923088303569263/100000000000000000000)
  directionHi := (35166995193018973079/6250000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree128.table
  base := (72576249182446385011678521879814293056421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 222605000000000000000000000000000000000000000
      center := (2226050)
      previous := (1113025)
      next := (1113025)
      square := (20488480998206750513870866216840000000000000)
      linear := (-2760360947354142758639636106647590500000000000)
      constant := (96205254858988298320315684873253836141164919341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree128.table
  base := (145152498364367738264328187802474985230177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-15524176268478682382431563319707187429000000000000)
      constant := (541591088142028704254379112965085706620168482999553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell124.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562671923088303569263/100000000000000000000)
  centralHi := (35166995193018973079/6250000000000000000)
  directionLo := (564882823248012069619/100000000000000000000)
  directionHi := (28244141162400603481/5000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree129.table
  base := (148282907367922505355327379958759326008617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (4452100)
      previous := (2226050)
      next := (2226050)
      square := (40976961996413501027741732433680000000000000)
      linear := (-5563835096429630527839265884386541000000000000)
      constant := (195465484879987944816749238451354932953229637457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree129.table
  base := (148282907367476923767190198450692145201317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (12505948900)
      previous := (6252974450)
      next := (6252974450)
      square := (115104286247925524386926526406207120000000000000)
      linear := (-15645409912006464801191414351744700669000000000000)
      constant := (550189920811706097782698595983603390949940506147013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell124.Kernel129
