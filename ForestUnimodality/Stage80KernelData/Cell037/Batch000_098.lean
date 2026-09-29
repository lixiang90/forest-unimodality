import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell037.Parameters
import ForestUnimodality.BinomialMassData.Q1687_3572.Batch000_049
import ForestUnimodality.BinomialMassData.Q1687_3572.Batch050_099
import ForestUnimodality.BinomialMassData.Q9_19.Batch000_049
import ForestUnimodality.BinomialMassData.Q9_19.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree000.table
  base := (5532482752963936494360552881/100000000000000000000000000)
  polynomial :=
    { denominator := 35720000000000000000000000000000000000000000
      center := (224315)
      previous := (200753)
      next := (0)
      square := (6955559654446564554763909944000000000000000)
      linear := (30321958186835021500371567448400000000000000)
      constant := (1976202839358718115785589489093200000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree000.table
  base := (5532482752963936494360552881/100000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1190)
      previous := (1071)
      next := (0)
      square := (36997657736417896567893138000000000000000)
      linear := (161287011632101178193465784300000000000000)
      constant := (10511717230631479339285050473900000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree001.table
  base := (331658040761004393674496635933316794240133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (21210494092317996997888451693657200000000000000)
      constant := (1046518655750812883563834939927196976999999282868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree001.table
  base := (8275136708686296203063066185615954570449/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (2398495381754400247453773417700000000000000)
      constant := (118199117825406988127542080723594383997283560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49923125646186015803/100000000000000000000)
  directionHi := (12480781411546503951/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree002.table
  base := (207866544573596712061358809858664519651099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (15343479523792319795945093655893200000000000000)
      constant := (643017099999372288936038577849241250124996985804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree002.table
  base := (51785414678465188320015667572721800439981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (1732537542498878109231696933700000000000000)
      constant := (72505880012989036962830628105610279835332564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49923125646186015803/100000000000000000000)
  centralHi := (12480781411546503951/25000000000000000000)
  directionLo := (70601961364892348123/100000000000000000000)
  directionHi := (17650490341223087031/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree003.table
  base := (136912404765014322619726392321949696959287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (9476464955266642594001735618129200000000000000)
      constant := (410826831933326661888305436273983255561945835452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree003.table
  base := (136294473633949941823057999103763177619741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (1066579703243355971009620449700000000000000)
      constant := (46267097377781231218373735058358507120726501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70601961364892348123/100000000000000000000)
  centralHi := (17650490341223087031/25000000000000000000)
  directionLo := (86469390091839017747/100000000000000000000)
  directionHi := (21617347522959754437/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree004.table
  base := (1894985510332093287780172928370151997383/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (3609450386740965392058377580365200000000000000)
      constant := (273244913845721338078787024985871068032215193400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree004.table
  base := (9426568764142016972727799165490634396023/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (400621863987833832787543965700000000000000)
      constant := (30747210526449543801424139744621190169643030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86469390091839017747/100000000000000000000)
  centralHi := (21617347522959754437/25000000000000000000)
  directionLo := (99846251292372031607/100000000000000000000)
  directionHi := (12480781411546503951/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree005.table
  base := (68483689672808276379246999997640956984707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-2257564181784711809884980457398800000000000000)
      constant := (189143815777621371079557450372899134025990449772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree005.table
  base := (17028369015457755575654423271455228039599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-265335975267688305434532518300000000000000)
      constant := (21274220751520985008853953460481349289180956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99846251292372031607/100000000000000000000)
  centralHi := (12480781411546503951/12500000000000000000)
  directionLo := (55815751297067522967/50000000000000000000)
  directionHi := (22326300518827009187/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree006.table
  base := (25587248620694819062853884810025931302191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-8124578750310389011828338495162800000000000000)
      constant := (136382685248393866654291067935128751128007286072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree006.table
  base := (1017760688592165352416757168728469586659/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-931293814523210443656609002300000000000000)
      constant := (15339248640923257114568808775348876039194950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55815751297067522967/50000000000000000000)
  centralHi := (22326300518827009187/20000000000000000000)
  directionLo := (24457236839601693147/20000000000000000000)
  directionHi := (15285773024751058217/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree007.table
  base := (19529944880210497839799857754600083594573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-13991593318836066213771696532926800000000000000)
      constant := (102962120673415522968149376198311256499269154216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree007.table
  base := (1553275563950262355094227398749582082133/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-1597251653778732581878685486300000000000000)
      constant := (11585846208452039922114313900814978291250325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24457236839601693147/20000000000000000000)
  centralHi := (15285773024751058217/12500000000000000000)
  directionLo := (33021043782709734407/25000000000000000000)
  directionHi := (132084175130838937629/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree008.table
  base := (30080254803322934361957012577597995047641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-19858607887361743415715054570690800000000000000)
      constant := (82312378572833029395825902161678174210985071236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree008.table
  base := (29892379982558323150329268563419636106799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-2263209493034254720100761970300000000000000)
      constant := (9273003162802289606705541449794488634554439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33021043782709734407/25000000000000000000)
  centralHi := (132084175130838937629/100000000000000000000)
  directionLo := (141203922729784696247/100000000000000000000)
  directionHi := (17650490341223087031/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree009.table
  base := (23090331188787519236710432791024641635337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-25725622455887420617658412608454800000000000000)
      constant := (70780309411555060309986766518584437789831421252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree009.table
  base := (11465166579153779658729771662437441019461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-2929167332289776858322838454300000000000000)
      constant := (7989477717877139763192528633979832416050842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141203922729784696247/100000000000000000000)
  centralHi := (17650490341223087031/12500000000000000000)
  directionLo := (149769376938558047411/100000000000000000000)
  directionHi := (37442344234639511853/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree010.table
  base := (17438586715669447918576829717292955096031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-31592637024413097819601770646218800000000000000)
      constant := (66287658380497134743265329912225198993499299676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree010.table
  base := (2162332854696156216619207600667557338659/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-3595125171545298996544914938300000000000000)
      constant := (7501671904051549021444057163727905594047192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149769376938558047411/100000000000000000000)
  centralHi := (37442344234639511853/25000000000000000000)
  directionLo := (9866924059794570283/6250000000000000000)
  directionHi := (157870784956713124529/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree011.table
  base := (1592785615550201650641122292663730073161/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-37459651592938775021545128683982800000000000000)
      constant := (67613574251877932409788039698356564259589321248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree011.table
  base := (12617593982994919837850238538324912527897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-4261083010800821134766991422300000000000000)
      constant := (7672486932842718065675067968635293422570817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9866924059794570283/6250000000000000000)
  centralHi := (157870784956713124529/100000000000000000000)
  directionLo := (646782328633468673/390625000000000000)
  directionHi := (165576276130167980289/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree012.table
  base := (2191720910407194985583633787070244809949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-43326666161464452223488486721746800000000000000)
      constant := (74009915339297617636163142662861674455184321616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree012.table
  base := (4327221406743314337137647352122861779139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-4927040850056343272989067906300000000000000)
      constant := (8417923959274290210093053611832706204538358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (646782328633468673/390625000000000000)
  centralHi := (165576276130167980289/100000000000000000000)
  directionLo := (86469390091839017747/50000000000000000000)
  directionHi := (34587756036735607099/20000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree013.table
  base := (5361102793908479857103599527969963559189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-49193680729990129425431844759510800000000000000)
      constant := (84994129069609698894761566198810877881246835444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree013.table
  base := (1314761050356114830289317691111210104903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-5592998689311865411211144390300000000000000)
      constant := (9683773372275475446191181460864587391479932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86469390091839017747/50000000000000000000)
  centralHi := (34587756036735607099/20000000000000000000)
  directionLo := (180000389348754983947/100000000000000000000)
  directionHi := (45000097337188745987/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree014.table
  base := (2421734649971338783185680192579779430221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-55060695298515806627375202797274800000000000000)
      constant := (100237003834442051547574158198354410107401224916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree014.table
  base := (2328834247759586929509177493276979174463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-6258956528567387549433220874300000000000000)
      constant := (11433009604289648003485148405272989481981143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180000389348754983947/100000000000000000000)
  centralHi := (45000097337188745987/25000000000000000000)
  directionLo := (186795231844895501797/100000000000000000000)
  directionHi := (93397615922447750899/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree015.table
  base := (-12562245572338667518395816523372488021/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-60927709867041483829318560835038800000000000000)
      constant := (119501213498659474473764149037067125312005662840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree015.table
  base := (-210229730232517476653900622735238695731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-6924914367822909687655297358300000000000000)
      constant := (13638903246853252921644399944692578830841109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186795231844895501797/100000000000000000000)
  centralHi := (93397615922447750899/50000000000000000000)
  directionLo := (96675717109149413423/50000000000000000000)
  directionHi := (193351434218298826847/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree016.table
  base := (-2337277062180524732930976625166264816703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-66794724435567161031261918872802800000000000000)
      constant := (142607145309778522652674524705579949152740037412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree016.table
  base := (-2414262412328472842433035227849676259657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-7590872207078431825877373842300000000000000)
      constant := (16281196900566930761487449215546266870263823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96675717109149413423/50000000000000000000)
  centralHi := (193351434218298826847/100000000000000000000)
  directionLo := (39938500516948812643/20000000000000000000)
  directionHi := (12480781411546503951/6250000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree017.table
  base := (-4257538966955917547880567848495229994187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-72661739004092838233205276910566800000000000000)
      constant := (169413460052794760992643116953720909345462284148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree017.table
  base := (-2163735647560383854210921275318150232019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-8256830046333953964099450326300000000000000)
      constant := (19343931659160793159860000759320295532482282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39938500516948812643/20000000000000000000)
  centralHi := (12480781411546503951/6250000000000000000)
  directionLo := (25729790025025858349/12500000000000000000)
  directionHi := (205838320200206866793/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree018.table
  base := (-118445984243415307597212484386467183081/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-78528753572618515435148634948330800000000000000)
      constant := (199805672625114153389671953966248626263847926200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree018.table
  base := (-748211646487734754950549651231685388513/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-8922787885589476102321526810300000000000000)
      constant := (22814170440256256293402803638642892597974456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25729790025025858349/12500000000000000000)
  centralHi := (205838320200206866793/100000000000000000000)
  directionLo := (211805884094677044371/100000000000000000000)
  directionHi := (52951471023669261093/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree019.table
  base := (-3680611918379378244592023734351166618629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10542805)
      previous := (9435391)
      next := (0)
      square := (326911303758988534073903767368000000000000000)
      linear := (-4441882533744431191425894367689200000000000000)
      constant := (12299429179705798777145683318582177486796177928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree019.table
  base := (-3709281558075401860832647019730332129517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1190)
      previous := (1071)
      next := (0)
      square := (36997657736417896567893138000000000000000)
      linear := (-504670827623420960028610699700000000000000)
      constant := (1404274472754073747546511532550247379078354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211805884094677044371/100000000000000000000)
  centralHi := (52951471023669261093/25000000000000000000)
  directionLo := (217609859637408529951/100000000000000000000)
  directionHi := (6800308113669016561/3125000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree020.table
  base := (-4299584398415644637772091382925147409007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-90262782709669869839035351023858800000000000000)
      constant := (270984619991302516951182970566767792990678214856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree020.table
  base := (-4325457957739178022666610696139706069209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-10254703564100520378765679778300000000000000)
      constant := (30936099927046725013849690703387132218031102) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217609859637408529951/100000000000000000000)
  centralHi := (6800308113669016561/3125000000000000000)
  directionLo := (223263005188270091869/100000000000000000000)
  directionHi := (22326300518827009187/10000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree021.table
  base := (-4828572614887759131043185809564458420137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-96129797278195547040978709061622800000000000000)
      constant := (311625048113798177996605998745361857578561355896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree021.table
  base := (-9703744431749238802014423747650165934747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-10920661403356042516987756262300000000000000)
      constant := (35571246851281069656103064136398290097556333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223263005188270091869/100000000000000000000)
  centralHi := (22326300518827009187/10000000000000000000)
  directionLo := (57194125550609650143/25000000000000000000)
  directionHi := (228776502202438600573/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree022.table
  base := (-2638253820555743138459962964899338822733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-101996811846721224242922067099386800000000000000)
      constant := (355553462178020494888931224872282394482406270128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree022.table
  base := (-2648723059886537580552751357937070747389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-11586619242611564655209832746300000000000000)
      constant := (40580214224606081032832579755738869840770284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57194125550609650143/25000000000000000000)
  centralHi := (228776502202438600573/100000000000000000000)
  directionLo := (46832043062103224777/20000000000000000000)
  directionHi := (117080107655258061943/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree023.table
  base := (-11302018710879840942214201209144627356943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-107863826415246901444865425137150800000000000000)
      constant := (402721250468987093446075543568558704235332646372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree023.table
  base := (-2834894762307990953796199197964213119823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-12252577081867086793431909230300000000000000)
      constant := (45957507731580761915494716806039676254975588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46832043062103224777/20000000000000000000)
  centralHi := (117080107655258061943/50000000000000000000)
  directionLo := (239422899716280576281/100000000000000000000)
  directionHi := (119711449858140288141/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree024.table
  base := (-5958593630962071904832926248426879849877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-113730840983772578646808783174914800000000000000)
      constant := (453086844374866308964160955221713064724763489816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree024.table
  base := (-11950814935519491101659039476271611997673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-12918534921122608931653985714300000000000000)
      constant := (51698430735233787236808385052265948068840047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239422899716280576281/100000000000000000000)
  centralHi := (119711449858140288141/50000000000000000000)
  directionLo := (24457236839601693147/10000000000000000000)
  directionHi := (244572368396016931471/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree025.table
  base := (-12409680314538384268948126456335250450331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-119597855552298255848752141212678800000000000000)
      constant := (506614647752579309744139368368957643454535977524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree025.table
  base := (-6219868151818116384487089021926631831101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-13584492760378131069876062198300000000000000)
      constant := (57798962993278029284743684008668971817945078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24457236839601693147/10000000000000000000)
  centralHi := (244572368396016931471/100000000000000000000)
  directionLo := (249615628230930079019/100000000000000000000)
  directionHi := (12480781411546503951/5000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree026.table
  base := (-2557812461452620855978440380150725905201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-125464870120823933050695499250442800000000000000)
      constant := (563274151994327229204709128156775475552467355020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree026.table
  base := (-6407941905863022386972187290585009343467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-14250450599633653208098138682300000000000000)
      constant := (64255660328123556058890701161997623254016826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249615628230930079019/100000000000000000000)
  centralHi := (12480781411546503951/5000000000000000000)
  directionLo := (127279495924723450081/50000000000000000000)
  directionHi := (254558991849446900163/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree027.table
  base := (-6531767590387387090486226740244864650043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-131331884689349610252638857288206800000000000000)
      constant := (623039194582548024966086028222880383437502877544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree027.table
  base := (-13087435328751450075083390318081889700291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-14916408438889175346320215166300000000000000)
      constant := (71065570529074896771225968708272437818194949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127279495924723450081/50000000000000000000)
  centralHi := (254558991849446900163/100000000000000000000)
  directionLo := (129704085137758526621/50000000000000000000)
  directionHi := (259408170275517053243/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree028.table
  base := (-6620067432387430282350297701612079485109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-137198899257875287454582215325970800000000000000)
      constant := (685887332336823677697342572634469590613434504472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree028.table
  base := (-3315350720748842522364000785733546640891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-15582366278144697484542291650300000000000000)
      constant := (78226162253921916790189101829800758650553396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129704085137758526621/50000000000000000000)
  centralHi := (259408170275517053243/100000000000000000000)
  directionLo := (33021043782709734407/12500000000000000000)
  directionHi := (264168350261677875257/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree029.table
  base := (-13324898316548394430913484586513347243317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-143065913826400964656525573363734800000000000000)
      constant := (751799308594954224655323154543349271016656406668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree029.table
  base := (-6671900040302643662712819909752514408401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-16248324117400219622764368134300000000000000)
      constant := (85735264590845374930260903464858684597134478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33021043782709734407/12500000000000000000)
  centralHi := (264168350261677875257/100000000000000000000)
  directionLo := (134422129645997463867/50000000000000000000)
  directionHi := (53768851858398985547/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree030.table
  base := (-13323006035965830713851707541957084965379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-148932928394926641858468931401498800000000000000)
      constant := (820758598619174888172606888057164458205773927316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree030.table
  base := (-13339784913973592180974736722688920480879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-16914281956655741760986444618300000000000000)
      constant := (93591015504591618257769714082109299706402681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134422129645997463867/50000000000000000000)
  centralHi := (53768851858398985547/20000000000000000000)
  directionLo := (6836005514395188307/2500000000000000000)
  directionHi := (273440220575807532281/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree031.table
  base := (-13238903932131015886978606011952954032573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-154799942963452319060412289439262800000000000000)
      constant := (892751020866409855183526299539382315038714774892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree031.table
  base := (-13253781841347817413077427889682741965533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-17580239795911263899208521102300000000000000)
      constant := (101791817765733287447447871294124530150442587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6836005514395188307/2500000000000000000)
  centralHi := (273440220575807532281/100000000000000000000)
  directionLo := (138980099926960004361/50000000000000000000)
  directionHi := (277960199853920008723/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree032.table
  base := (-13076407680512110530176725721936611659879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-160666957531977996262355647477026800000000000000)
      constant := (967764404110313488943014364165191083873764605316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree032.table
  base := (-6544793143666892332983128443814126384811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-18246197635166786037430597586300000000000000)
      constant := (110336301225987680885727426873166200750166458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138980099926960004361/50000000000000000000)
  centralHi := (277960199853920008723/100000000000000000000)
  directionLo := (56481569091913878499/20000000000000000000)
  directionHi := (17650490341223087031/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree033.table
  base := (-6419396082470133713118909755366877472887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-166533972100503673464299005514790800000000000000)
      constant := (1045788302139540713629133079896315911408989877896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree033.table
  base := (-12850454170698669816701337876588752024401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-18912155474422308175652674070300000000000000)
      constant := (119223290498679848080989679607451460519191239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56481569091913878499/20000000000000000000)
  centralHi := (17650490341223087031/6250000000000000000)
  directionLo := (286786522785504871141/100000000000000000000)
  directionHi := (143393261392752435571/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree034.table
  base := (-2505773635636006687851221424076388063567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-172400986669029350666242363552554800000000000000)
      constant := (1126813749098574348712982160976484368301931188340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree034.table
  base := (-6269589322346319033493338959989780790161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-19578113313677830313874750554300000000000000)
      constant := (128451777255486479395419482947087378269503758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286786522785504871141/100000000000000000000)
  centralHi := (143393261392752435571/50000000000000000000)
  directionLo := (36387418010403545543/12500000000000000000)
  directionHi := (58219868816645672869/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree035.table
  base := (-12149048218525763444194821726652602195851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-178268001237555027868185721590318800000000000000)
      constant := (1210833049610005054191823386074553436126083263604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree035.table
  base := (-1519769487199851624700037267444846899637/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-20244071152933352452096827038300000000000000)
      constant := (138020896472437367216355971267119282153848344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36387418010403545543/12500000000000000000)
  centralHi := (58219868816645672869/20000000000000000000)
  directionLo := (73837298586135760841/25000000000000000000)
  directionHi := (59069838868908608673/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree036.table
  base := (-234028058889769459324834920174010014181/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-184135015806080705070129079628082800000000000000)
      constant := (1297839598695597026787474866751685977640275146200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree036.table
  base := (-2927360396081677097417949006459744212273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-20910028992188874590318903522300000000000000)
      constant := (147929906058110177068811359873472129357477788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73837298586135760841/25000000000000000000)
  centralHi := (59069838868908608673/20000000000000000000)
  directionLo := (299538753877116094823/100000000000000000000)
  directionHi := (37442344234639511853/12500000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree037.table
  base := (-2237541924060774457724320578227133796373/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-190002030374606382272072437665846800000000000000)
      constant := (1387827727245000254781347514721852607624322950460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree037.table
  base := (-11194799229036532449112447441184624344071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-21575986831444396728540980006300000000000000)
      constant := (158178169380283073790451678179832350611790369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299538753877116094823/100000000000000000000)
  centralHi := (37442344234639511853/12500000000000000000)
  directionLo := (151835259037995196673/50000000000000000000)
  directionHi := (303670518075990393347/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree038.table
  base := (-10609493691898623195292852893152185141519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10542805)
      previous := (9435391)
      next := (0)
      square := (326911303758988534073903767368000000000000000)
      linear := (-10308897102270108393369252405453200000000000000)
      constant := (77936451020889455585348303602882638549701224204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree038.table
  base := (-10615741744323627857399785566412036168259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1190)
      previous := (1071)
      next := (0)
      square := (36997657736417896567893138000000000000000)
      linear := (-1170628666878943098250687183700000000000000)
      constant := (8882375804079428351224396668838171312803079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151835259037995196673/50000000000000000000)
  centralHi := (303670518075990393347/100000000000000000000)
  directionLo := (38468351850666088349/12500000000000000000)
  directionHi := (307746814805328706793/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree039.table
  base := (-9734437958214304515270137047031315413/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-201736059511657736675959153741374800000000000000)
      constant := (1576729948719689934689355867114502162978175234048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree039.table
  base := (-9973567047562170594821106676276291593121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-22907902509955441004985132974300000000000000)
      constant := (179690350201616294188363221502564258734883319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38468351850666088349/12500000000000000000)
  centralHi := (307746814805328706793/100000000000000000000)
  directionLo := (155884909867111704359/50000000000000000000)
  directionHi := (311769819734223408719/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree040.table
  base := (-2316136437821719472395353918183876191137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-207603074080183413877902511779138800000000000000)
      constant := (1675636280523674039395219911773462977844063847792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree040.table
  base := (-579336788407530973160442285191996169661/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-23573860349210963143207209458300000000000000)
      constant := (190953397187852171433532902212731030124038064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155884909867111704359/50000000000000000000)
  centralHi := (311769819734223408719/100000000000000000000)
  directionLo := (315741569913426249057/100000000000000000000)
  directionHi := (157870784956713124529/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree041.table
  base := (-8499902111408035738360947375651258763833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-213470088648709091079845869816902800000000000000)
      constant := (1777508488016851759714872800080035917400160551932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree041.table
  base := (-2126040422592922654451526711570707413061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-24239818188466485281429285942300000000000000)
      constant := (202553936392709285700998782243791898495539916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315741569913426249057/100000000000000000000)
  centralHi := (157870784956713124529/50000000000000000000)
  directionLo := (63932795166699824753/20000000000000000000)
  directionHi := (159831987916749561883/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree042.table
  base := (-7674961457566391268614025243476229800709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-219337103217234768281789227854666800000000000000)
      constant := (1882343930341623536931516051093985096086617634636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree042.table
  base := (-1919676443892246427682476919437938925021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-24905776027722007419651362426300000000000000)
      constant := (214491671976524020970077654230931616192269676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63932795166699824753/20000000000000000000)
  centralHi := (159831987916749561883/50000000000000000000)
  directionLo := (64707766433393383731/20000000000000000000)
  directionHi := (631911781576107263/195312500000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree043.table
  base := (-6790434396205611858158236722033634355401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-225204117785760445483732585892430800000000000000)
      constant := (1990140340808397786618056635650973401267679311804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree043.table
  base := (-6793723916139589199440078767239516080121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-25571733866977529557873438910300000000000000)
      constant := (226766350139680555026382840678926534695076319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64707766433393383731/20000000000000000000)
  centralHi := (631911781576107263/195312500000000000)
  directionLo := (163683913682934695107/50000000000000000000)
  directionHi := (65473565473173878043/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree044.table
  base := (-146173271306969946666786700143516930981/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-231071132354286122685675943930194800000000000000)
      constant := (2100895773880998809059595471079593610704981204960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree044.table
  base := (-5849819252607970700137245405563980919369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-26237691706233051696095515394300000000000000)
      constant := (239377753148449554338465915857791402888107791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163683913682934695107/50000000000000000000)
  centralHi := (65473565473173878043/20000000000000000000)
  directionLo := (331152552260335960577/100000000000000000000)
  directionHi := (165576276130167980289/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree045.table
  base := (-4844974334417861171931810832004802136317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-236938146922811799887619301967958800000000000000)
      constant := (2214608559673686566276043511468230410164784578668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree045.table
  base := (-605938652145742192007716463906825387623/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-26903649545488573834317591878300000000000000)
      constant := (252325694209809776462637122760737088280544776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331152552260335960577/100000000000000000000)
  centralHi := (165576276130167980289/50000000000000000000)
  directionLo := (83723626945601284451/25000000000000000000)
  directionHi := (66978901556481027561/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree046.table
  base := (-3785014178899345295664021297692775309353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-242805161491337477089562660005722800000000000000)
      constant := (2331277264895403484847977216718122576089327038012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree046.table
  base := (-1893618856657399838404353128211381546701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-27569607384744095972539668362300000000000000)
      constant := (265610013074597248499872605533231382523281878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83723626945601284451/25000000000000000000)
  centralHi := (66978901556481027561/20000000000000000000)
  directionLo := (84648777980364360407/25000000000000000000)
  directionHi := (338595111921457441629/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree047.table
  base := (-666859014699568043740254204793886228463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 678680000000000000000000000000000000000000000
      center := (4261985)
      previous := (3814307)
      next := (0)
      square := (132155633434484726540514288936000000000000000)
      linear := (-5290897362975811793436298256244400000000000000)
      constant := (52146822538887607491500964834599994117786692464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree047.table
  base := (-1334692782348151551187163254755151092371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-28235565223999618110761744846300000000000000)
      constant := (279230572265477300151393751329166780911308138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84648777980364360407/25000000000000000000)
  centralHi := (338595111921457441629/100000000000000000000)
  directionLo := (17112785300133725397/5000000000000000000)
  directionHi := (342255706002674507941/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree048.table
  base := (-74628550206819662881698408949465190761/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-254539190628388831493449376081250800000000000000)
      constant := (2573477687052389505352525621675011034647426504880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree048.table
  base := (-1494279479077947120067973157806583007633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-28901523063255140248983821330300000000000000)
      constant := (293187253840945864167261873720431823534244487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17112785300133725397/5000000000000000000)
  centralHi := (342255706002674507941/100000000000000000000)
  directionLo := (345877560367356070989/100000000000000000000)
  directionHi := (34587756036735607099/10000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree049.table
  base := (-65175785999991892356764338437717687291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-260406205196914508695392734119014800000000000000)
      constant := (2699007441755596511908635351372272087487799669456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree049.table
  base := (-262199738501528366847126140673284939419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-29567480902510662387205897814300000000000000)
      constant := (307479956619185851961535322448916944136869741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345877560367356070989/100000000000000000000)
  centralHi := (34587756036735607099/10000000000000000000)
  directionLo := (349461879523302110627/100000000000000000000)
  directionHi := (87365469880825527657/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree050.table
  base := (1027923648292064765796818293511425765077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-266273219765440185897336092156778800000000000000)
      constant := (2827489145531201309837537161760984571859739554292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree050.table
  base := (64163325211481515204266685141598796053/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-30233438741766184525427974298300000000000000)
      constant := (322108593796429884676252896438377874646002128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349461879523302110627/100000000000000000000)
  centralHi := (87365469880825527657/25000000000000000000)
  directionLo := (353009806824461740619/100000000000000000000)
  directionHi := (17650490341223087031/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree051.table
  base := (2373100051546302875047249199335731773629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-272140234333965863099279450194542800000000000000)
      constant := (2958922130687298473808169736377256119868594689684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree051.table
  base := (296494132688380687813513006747233716311/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-30899396581021706663650050782300000000000000)
      constant := (337073090903767437731409588831786010972706168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353009806824461740619/100000000000000000000)
  centralHi := (17650490341223087031/5000000000000000000)
  directionLo := (71304485746277890339/20000000000000000000)
  directionHi := (22282651795711840731/6250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree052.table
  base := (3774646401178093633279697478843776736239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-278007248902491540301222808232306800000000000000)
      constant := (3093305824130514535620878508454053563658148217244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree052.table
  base := (23585267899088851830498070919937904941/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-31565354420277228801872127266300000000000000)
      constant := (352373384054301356365410037171935613389392160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71304485746277890339/20000000000000000000)
  centralHi := (22282651795711840731/6250000000000000000)
  directionLo := (72000155739501993579/20000000000000000000)
  directionHi := (45000097337188745987/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree053.table
  base := (1046481697463935249462281180720545320091/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-283874263471017217503166166270070800000000000000)
      constant := (3230639733962830151368612291715150762899224957180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree053.table
  base := (5231530785942464369784356449968197853807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-32231312259532750940094203750300000000000000)
      constant := (368009418439393367017954120725338519425224327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72000155739501993579/20000000000000000000)
  centralHi := (45000097337188745987/12500000000000000000)
  directionLo := (363445840720592677681/100000000000000000000)
  directionHi := (181722920360296338841/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree054.table
  base := (134925078965527402958472591660934681661/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-289741278039542894705109524307834800000000000000)
      constant := (3370923437977441075750399410583600340191176557800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree054.table
  base := (1686371644310063560520504842585470332277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-32897270098788273078316280234300000000000000)
      constant := (383981147038601585376740270614893419159807988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363445840720592677681/100000000000000000000)
  centralHi := (181722920360296338841/50000000000000000000)
  directionLo := (73371710518805079441/20000000000000000000)
  directionHi := (183429276297012698603/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree055.table
  base := (4158034587489205160078425151288502729923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-295608292608068571907052882345598800000000000000)
      constant := (3514156573784591008600582053696547921707794931416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree055.table
  base := (8315398495412805140592280145113611255183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-33563227938043795216538356718300000000000000)
      constant := (400288529512943155584094362453886013663121063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73371710518805079441/20000000000000000000)
  centralHi := (183429276297012698603/50000000000000000000)
  directionLo := (370239808888331421133/100000000000000000000)
  directionHi := (185119904444165710567/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree056.table
  base := (198835133080551858079020963345231179661/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-301475307176594249108996240383362800000000000000)
      constant := (3660338830336432412839156209833219051797896957800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree056.table
  base := (9941170676228508344151190719453062880243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-34229185777299317354760433202300000000000000)
      constant := (416931531255430466891676210994522555699767723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370239808888331421133/100000000000000000000)
  centralHi := (185119904444165710567/50000000000000000000)
  directionLo := (74718092737958200719/20000000000000000000)
  directionHi := (93397615922447750899/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree057.table
  base := (5811616343598035191842964620632765020453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10542805)
      previous := (9435391)
      next := (0)
      square := (326911303758988534073903767368000000000000000)
      linear := (-16175911670795785595312610443217200000000000000)
      constant := (200498417929089099651167701467277022245387462904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree057.table
  base := (11622720877216314043032316792899713356507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1190)
      previous := (1071)
      next := (0)
      square := (36997657736417896567893138000000000000000)
      linear := (-1836586506134465236472763667700000000000000)
      constant := (22837374872449024753588135444965094553773633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74718092737958200719/20000000000000000000)
  centralHi := (93397615922447750899/25000000000000000000)
  directionLo := (75382266623984695937/20000000000000000000)
  directionHi := (188455666559961739843/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree058.table
  base := (2672085086807873510640015037815917411087/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-313209336313645603512882956458890800000000000000)
      constant := (3961549675577010024964959540270746710471078341260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree058.table
  base := (1669997317745241092665180520152886160183/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-35561101455810361631204586170300000000000000)
      constant := (451224278005380605911564418505601535230608504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75382266623984695937/20000000000000000000)
  centralHi := (188455666559961739843/50000000000000000000)
  directionLo := (190101598828444103439/50000000000000000000)
  directionHi := (380203197656888206879/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree059.table
  base := (15153273231842913710691514280843662331013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-319076350882171280714826314496654800000000000000)
      constant := (4116577838417903520851150724794648190728815943348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree059.table
  base := (189411039243477534560596153127818660899/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-36227059295065883769426662654300000000000000)
      constant := (468873975690291512639470058261031402926763120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190101598828444103439/50000000000000000000)
  centralHi := (380203197656888206879/100000000000000000000)
  directionLo := (383466804277511977159/100000000000000000000)
  directionHi := (9586670106937799429/2500000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree060.table
  base := (3400344630721571878401146712761888196437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-324943365450696957916769672534418800000000000000)
      constant := (4274554260349044159005397672651343099607209784260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree060.table
  base := (8500691369780038923271098363064110392363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-36893017134321405907648739138300000000000000)
      constant := (486859196884460164467479632696132287703286086) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383466804277511977159/100000000000000000000)
  centralHi := (9586670106937799429/2500000000000000000)
  directionLo := (386702868436597653693/100000000000000000000)
  directionHi := (193351434218298826847/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree061.table
  base := (18905729770349378488390949294666003376107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-330810380019222635118713030572182800000000000000)
      constant := (4435478796461237857045308379063553238905092604172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree061.table
  base := (18905432790589322906496268227048671613397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-37558974973576928045870815622300000000000000)
      constant := (505179925504752379975746104951264570452436317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386702868436597653693/100000000000000000000)
  centralHi := (193351434218298826847/50000000000000000000)
  directionLo := (194956037949185758079/50000000000000000000)
  directionHi := (389912075898371516159/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree062.table
  base := (20865254088759263999600137550389135876509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-336677394587748312320656388609946800000000000000)
      constant := (4599351322373786069514322888109711664062344902164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree062.table
  base := (10432497535509884113096539116386955244361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-38224932812832450184092892106300000000000000)
      constant := (523836147753189991895884899930631381686428642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194956037949185758079/50000000000000000000)
  centralHi := (389912075898371516159/100000000000000000000)
  directionLo := (49136885554168708691/12500000000000000000)
  directionHi := (393095084433349669529/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree063.table
  base := (22880262639386173211790367185256137868257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-342544409156273989522599746647710800000000000000)
      constant := (4766171731325966781229195873392916687547614705572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree063.table
  base := (11440018394931014496741125412048588622087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-38890890652087972322314968590300000000000000)
      constant := (542827851792225832310709731927399080985146814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49136885554168708691/12500000000000000000)
  centralHi := (393095084433349669529/100000000000000000000)
  directionLo := (99063131348129203221/25000000000000000000)
  directionHi := (79250505078503362577/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree064.table
  base := (779710209187727980290036821708000584009/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-348411423724799666724543104685474800000000000000)
      constant := (4935939931680609783332700826631279789787826309248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree064.table
  base := (6237632453748505665855638788906852645881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-39556848491343494460537045074300000000000000)
      constant := (562155027466163829421496816606381495220652164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99063131348129203221/25000000000000000000)
  centralHi := (79250505078503362577/20000000000000000000)
  directionLo := (399385005169488126431/100000000000000000000)
  directionHi := (12480781411546503951/3125000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree065.table
  base := (6769155398471709911769185549841906590639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-354278438293325343926486462723238800000000000000)
      constant := (5108655844781378285194429353487136057100775678576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree065.table
  base := (27076450011132489319768052264986557872783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-40222806330599016598759121558300000000000000)
      constant := (581817666062166726398481370002160147392074663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399385005169488126431/100000000000000000000)
  centralHi := (12480781411546503951/3125000000000000000)
  directionLo := (402493106560245244371/100000000000000000000)
  directionHi := (100623276640061311093/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree066.table
  base := (29257926173210245069108886020311010734167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-360145452861851021128429820761002800000000000000)
      constant := (5284319403113641663471163100383487780795802959932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree066.table
  base := (29257776671882046781940547415515567404381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-40888764169854538736981198042300000000000000)
      constant := (601815760105225790274474663814801119832981541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402493106560245244371/100000000000000000000)
  centralHi := (100623276640061311093/25000000000000000000)
  directionLo := (32446191202326531/8000000000000000)
  directionHi := (405577390029081637501/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree067.table
  base := (15747311132104527727051267750242841656909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-366012467430376698330373178798766800000000000000)
      constant := (5462930548725924767709695560555651830691683401128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree067.table
  base := (31494492032492814302253069608930645549561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-41554722009110060875203274526300000000000000)
      constant := (622149303182266314099561701513923963043391521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32446191202326531/8000000000000000)
  centralHi := (405577390029081637501/100000000000000000000)
  directionLo := (51079799361068162439/12500000000000000000)
  directionHi := (408638394888545299513/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree068.table
  base := (33786694272402045586200477777003031198517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-371879481998902375532316536836530800000000000000)
      constant := (5644489231875013763641386259842437560904904732532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree068.table
  base := (33786580851857447499606367920397678934673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-42220679848365583013425351010300000000000000)
      constant := (642818289791248546552165653515663562095416953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51079799361068162439/12500000000000000000)
  centralHi := (408638394888545299513/100000000000000000000)
  directionLo := (82335328080082746717/20000000000000000000)
  directionHi := (205838320200206866793/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree069.table
  base := (1806706440600905848351871577188856902117/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-377746496567428052734259894874294800000000000000)
      constant := (5828995409863029544360543617394817339818903962640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree069.table
  base := (36134030053908262300756561242358058215103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-42886637687621105151647427494300000000000000)
      constant := (663822715211712053681845478740191259015652183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82335328080082746717/20000000000000000000)
  centralHi := (205838320200206866793/50000000000000000000)
  directionLo := (82938525360813218877/20000000000000000000)
  directionHi := (207346313402033047193/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree070.table
  base := (7707382878614811706940450417572473969491/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-383613511135953729936203252912058800000000000000)
      constant := (6016449046039269623154727711452016035889932569180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree070.table
  base := (38536828419973351840663754348309665029633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-43552595526876627289869503978300000000000000)
      constant := (685162575393716277110321775010739789075697513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82938525360813218877/20000000000000000000)
  centralHi := (207346313402033047193/50000000000000000000)
  directionLo := (52210854534752474337/12500000000000000000)
  directionHi := (417686836278019794697/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree071.table
  base := (10248760288197102750571409788562496459109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-389480525704479407138146610949822800000000000000)
      constant := (6206850108943473152316392403697807787821120207056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree071.table
  base := (20497483162425065206902844214313121746701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-44218553366132149428091580462300000000000000)
      constant := (706837866862563083397901006897034073901118122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52210854534752474337/12500000000000000000)
  centralHi := (417686836278019794697/100000000000000000000)
  directionLo := (210329866919932574729/50000000000000000000)
  directionHi := (420659733839865149459/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree072.table
  base := (21754250312524819934818594294230448909217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-395347540273005084340089968987586800000000000000)
      constant := (6400198571570471423543095935561851818017649499464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree072.table
  base := (43508435510383808477431311872908890532509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-44884511205387671566313656946300000000000000)
      constant := (728848586637058593519650044767720109482235749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210329866919932574729/50000000000000000000)
  centralHi := (420659733839865149459/100000000000000000000)
  directionLo := (423611768189354088743/100000000000000000000)
  directionHi := (52951471023669261093/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree073.table
  base := (46077285542546865003928335574426615583531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-401214554841530761542033327025350800000000000000)
      constant := (6596494410739025260630662282308112120681884849676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree073.table
  base := (1439913402850660491788821338964785599211/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-45550469044643193704535733430300000000000000)
      constant := (751194732159390284119327187220621203242085472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423611768189354088743/100000000000000000000)
  centralHi := (52951471023669261093/12500000000000000000)
  directionLo := (85308674499794202477/20000000000000000000)
  directionHi := (213271686249485506193/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree074.table
  base := (48701389666935330935896460297347634879767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-407081569410056438743976685063114800000000000000)
      constant := (6795737606550087515962259416301820496348941257532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree074.table
  base := (6087667548520890822598689571962998418119/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-46216426883898715842757809914300000000000000)
      constant := (773876301234968765390838314652029139431527672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85308674499794202477/20000000000000000000)
  centralHi := (213271686249485506193/50000000000000000000)
  directionLo := (429454965155929727613/100000000000000000000)
  directionHi := (214727482577964863807/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree075.table
  base := (12845201910766124796607819991769227588643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-412948583978582115945920043100878800000000000000)
      constant := (6997928141921820422499375273940097060341372347312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree075.table
  base := (3211297799076389471586840165044809267349/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-46882384723154237980979886398300000000000000)
      constant := (796893291980818199978154658140798818328207824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429454965155929727613/100000000000000000000)
  centralHi := (214727482577964863807/50000000000000000000)
  directionLo := (13510842201849846523/3125000000000000000)
  directionHi := (432346950459195088737/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree076.table
  base := (54115534873859437963403636960441631980591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10542805)
      previous := (9435391)
      next := (0)
      square := (326911303758988534073903767368000000000000000)
      linear := (-22042926239321462797255968480981200000000000000)
      constant := (379108736957394355321642286144903982943429539444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree076.table
  base := (2164619904277393385782106953155816778603/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1190)
      previous := (1071)
      next := (0)
      square := (36997657736417896567893138000000000000000)
      linear := (-2502544345389987374694840151700000000000000)
      constant := (43170826462173713395271239415949012969836425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13510842201849846523/3125000000000000000)
  centralHi := (432346950459195088737/100000000000000000000)
  directionLo := (217609859637408529951/50000000000000000000)
  directionHi := (435219719274817059903/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree077.table
  base := (28452783706464619255719536278402402192707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-424682613115633470349806759176406800000000000000)
      constant := (7411151174767922566613485477811803337809376035544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree077.table
  base := (56905535013182160322776547066506403258423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-48214300401665282257424039366300000000000000)
      constant := (843933532250131507011298525569108811576290703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217609859637408529951/50000000000000000000)
  centralHi := (435219719274817059903/100000000000000000000)
  directionLo := (438073649652584609947/100000000000000000000)
  directionHi := (109518412413146152487/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree078.table
  base := (59750901872390799302098750214786574770569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-430549627684159147551750117214170800000000000000)
      constant := (7622183648847453903283213310071632757056861913924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree078.table
  base := (59750873708902922076584060588169798324493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-48880258240920804395646115850300000000000000)
      constant := (867956779197793933053834390501729297195141973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438073649652584609947/100000000000000000000)
  centralHi := (109518412413146152487/25000000000000000000)
  directionLo := (13778409606461054883/3125000000000000000)
  directionHi := (440909107406753756257/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree079.table
  base := (3132576767187609319629647899562027357963/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-436416642252684824753693475251934800000000000000)
      constant := (7836163415151590824197412081535263332366418910960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree079.table
  base := (62651510866656994270343469272787458484673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-49546216080176326533868192334300000000000000)
      constant := (892315442603581947283298083712176272512966953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13778409606461054883/3125000000000000000)
  centralHi := (440909107406753756257/100000000000000000000)
  directionLo := (443726446663375244827/100000000000000000000)
  directionHi := (110931611665843811207/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree080.table
  base := (65607465330005223966892188954682830985729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-442283656821210501955636833289698800000000000000)
      constant := (8053090465715386638170814135110675475546954421284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree080.table
  base := (16401861015047330997370983992925123882057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-50212173919431848672090268818300000000000000)
      constant := (917009521591617475597529532989783878885690308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443726446663375244827/100000000000000000000)
  centralHi := (110931611665843811207/25000000000000000000)
  directionLo := (446526010376540183739/100000000000000000000)
  directionHi := (22326300518827009187/5000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree081.table
  base := (68618689687339137319049322627637311216109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-448150671389736179157580191327462800000000000000)
      constant := (8272964793700522311289488169687297784767899623764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree081.table
  base := (34309335603717164111734927190815606865621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-50878131758687370810312345302300000000000000)
      constant := (942039015410274842529725384459068868156978362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446526010376540183739/100000000000000000000)
  centralHi := (22326300518827009187/5000000000000000000)
  directionLo := (89861626163134828447/20000000000000000000)
  directionHi := (112327032703918535559/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree082.table
  base := (71685206575112093154562617909116034868639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-454017685958261856359523549365226800000000000000)
      constant := (8495786393235725886277965709508163291559845207644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree082.table
  base := (35842595260809620289486904564626907048439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-51544089597942892948534421786300000000000000)
      constant := (967403923414529079411894441170260626888972958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89861626163134828447/20000000000000000000)
  centralHi := (112327032703918535559/25000000000000000000)
  directionLo := (220738833020429571/48828125000000000)
  directionHi := (452073130025839761409/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree083.table
  base := (74807014412910622091076818110575792499853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-459884700526787533561466907402990800000000000000)
      constant := (8721555259279800800154287486209183620612861099988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree083.table
  base := (74807000469315511948174218863841859015363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-52210047437198415086756498270300000000000000)
      constant := (993104245050812480016113112255746911104546043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220738833020429571/48828125000000000)
  centralHi := (452073130025839761409/100000000000000000000)
  directionLo := (227410660131426501437/50000000000000000000)
  directionHi := (3638570562102824023/800000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree084.table
  base := (15596822368738536591716741455316402102399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-465751715095313210763410265440754800000000000000)
      constant := (8950271387504059778162525972568577390803119603020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree084.table
  base := (77984099734450918620835605236742223222139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-52876005276453937224978574754300000000000000)
      constant := (1019139979844022971582986390031663942583192179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227410660131426501437/50000000000000000000)
  centralHi := (3638570562102824023/800000000000000000)
  directionLo := (57194125550609650143/12500000000000000000)
  directionHi := (91510600880975440229/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree085.table
  base := (5076031106384525950896234356234830100111/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-471618729663838887965353623478518800000000000000)
      constant := (9181934774191414847566880009361094977824218677696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree085.table
  base := (81216487187435339051433533656675870684007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-53541963115709459363200651238300000000000000)
      constant := (1045511127386378520234579953610559989316926527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57194125550609650143/12500000000000000000)
  centralHi := (91510600880975440229/20000000000000000000)
  directionLo := (460268476342030675173/100000000000000000000)
  directionHi := (230134238171015337587/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree086.table
  base := (84504170987566752425251811496958895490883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-477485744232364565167296981516282800000000000000)
      constant := (9416545416149763573951334850498823297001236629868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree086.table
  base := (21126040464668382402913484285224119901341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-54207920954964981501422727722300000000000000)
      constant := (1072217687327855243021072424811663629137536404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460268476342030675173/100000000000000000000)
  centralHi := (230134238171015337587/50000000000000000000)
  directionLo := (462968021345426543089/100000000000000000000)
  directionHi := (46296802134542654309/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree087.table
  base := (87847130840488892736211578026490162623209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-483352758800890242369240339554046800000000000000)
      constant := (9654103310637645986545673414370936814774861575364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree087.table
  base := (17569424583168298714620867321730064420747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-54873878794220503639644804206300000000000000)
      constant := (1099259659367984177123514118686822766279448335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462968021345426543089/100000000000000000000)
  centralHi := (46296802134542654309/10000000000000000000)
  directionLo := (465651916416956457829/100000000000000000000)
  directionHi := (46565191641695645783/10000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree088.table
  base := (4562268826137179661484096593723794117911/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-489219773369415919571183697591810800000000000000)
      constant := (9894608455300433648192507473999126071642720723120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree088.table
  base := (45622684822195813515532651342568809202471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-55539836633476025777866880690300000000000000)
      constant := (1126637043248813637532301321231734680244184062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465651916416956457829/100000000000000000000)
  centralHi := (46565191641695645783/10000000000000000000)
  directionLo := (468320430621032247771/100000000000000000000)
  directionHi := (117080107655258061943/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree089.table
  base := (47349453700128239205935318319138843086867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-495086787937941596773127055629574800000000000000)
      constant := (10138060848115558652239240528875200810246232018264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree089.table
  base := (94698901430827825828543695365075964007599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-56205794472731547916088957174300000000000000)
      constant := (1154349838748871530646759508904492423006743239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468320430621032247771/100000000000000000000)
  centralHi := (117080107655258061943/25000000000000000000)
  directionLo := (470973825399410020041/100000000000000000000)
  directionHi := (235486912699705010021/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree090.table
  base := (12275965366039479362866408940844644324391/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-500953802506467273975070413667338800000000000000)
      constant := (10384460487345501754193691985345270864698920913888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree090.table
  base := (98207717748356937763544621999933287840627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-56871752311987070054311033658300000000000000)
      constant := (1182398045677985528521968525458975916910466347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470973825399410020041/100000000000000000000)
  centralHi := (235486912699705010021/50000000000000000000)
  directionLo := (236806177435069686793/50000000000000000000)
  directionHi := (473612354870139373587/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree091.table
  base := (12721477829865281877814088704911752492341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-506820817074992951177013771705102800000000000000)
      constant := (10633807371497440315434708540226245307624474819488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree091.table
  base := (50885909072289439613661478596324278176163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-57537710151242592192533110142300000000000000)
      constant := (1210781663872839200975171380626846128843189686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236806177435069686793/50000000000000000000)
  centralHi := (473612354870139373587/100000000000000000000)
  directionLo := (119059066527901316609/25000000000000000000)
  directionHi := (476236266111605266437/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree092.table
  base := (105391206129930321956915745183069084968961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-512687831643518628378957129742866800000000000000)
      constant := (10886101499288612493991619721677012634957651921956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree092.table
  base := (105391202230925721593687698430334215279399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-58203667990498114330755186626300000000000000)
      constant := (1239500693193159525772313122500950651715863039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119059066527901316609/25000000000000000000)
  centralHi := (476236266111605266437/100000000000000000000)
  directionLo := (239422899716280576281/50000000000000000000)
  directionHi := (478845799432561152563/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree093.table
  base := (21813174611145688130068326590438037781043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-518554846212044305580900487780630800000000000000)
      constant := (11141342869616587806401818915434798855809099186140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree093.table
  base := (27266467418400304929763816275404821832683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-58869625829753636468977263110300000000000000)
      constant := (1268555133518446058416560078480584562726394252) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239422899716280576281/50000000000000000000)
  centralHi := (478845799432561152563/100000000000000000000)
  directionLo := (481441188628988679423/100000000000000000000)
  directionHi := (1880629643081987029/390625000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree094.table
  base := (112795823119238891743349778190455242236677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 678680000000000000000000000000000000000000000
      center := (4261985)
      previous := (3814307)
      next := (0)
      square := (132155633434484726540514288936000000000000000)
      linear := (-11157911931501488995379656294008400000000000000)
      constant := (242543223011356360250285956385290416380118794636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree094.table
  base := (56397910092903785931112241888636099418497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-59535583669009158607199339594300000000000000)
      constant := (1297944984745164792479338624957795263780154834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481441188628988679423/100000000000000000000)
  centralHi := (1880629643081987029/390625000000000000)
  directionLo := (96804532245712201347/20000000000000000000)
  directionHi := (30251416326785062921/6250000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree095.table
  base := (58290528032525531079956735586870967151379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1678840000000000000000000000000000000000000000
      center := (10542805)
      previous := (9435391)
      next := (0)
      square := (326911303758988534073903767368000000000000000)
      linear := (-27909940807847139999199326518745200000000000000)
      constant := (613719333380283585164685533217231490898484224072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree095.table
  base := (116581053521076498527121548445395751519843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 190000000000000000000000000000000000000000
      center := (1190)
      previous := (1071)
      next := (0)
      square := (36997657736417896567893138000000000000000)
      linear := (-3168502184645509512916916635700000000000000)
      constant := (69877381409702141003292953576962519278877017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96804532245712201347/20000000000000000000)
  centralHi := (30251416326785062921/6250000000000000000)
  directionLo := (486590438723433210773/100000000000000000000)
  directionHi := (243295219361716605387/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree096.table
  base := (3763174114797728358827775491986542950973/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-536155889917621337186730561893922800000000000000)
      constant := (11924750426990906085886070608700307416282939888256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree096.table
  base := (120421569467547720368381328973147832049283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-60867499347520202883643492562300000000000000)
      constant := (1357730919559492157322565745516106367369791163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486590438723433210773/100000000000000000000)
  centralHi := (243295219361716605387/50000000000000000000)
  directionLo := (24457236839601693147/5000000000000000000)
  directionHi := (489144736792033862941/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree097.table
  base := (124317369755743647893853062516508345862247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-542022904486147014388673919931686800000000000000)
      constant := (12191780759227673879909518525735111855598012031612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree097.table
  base := (124317367843060214226061345029765131612667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-61533457186775725021865569046300000000000000)
      constant := (1388127003004859097898598272219845212512172787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell037.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24457236839601693147/5000000000000000000)
  centralHi := (489144736792033862941/100000000000000000000)
  directionLo := (245842882755243171849/50000000000000000000)
  directionHi := (491685765510486343699/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1687
  qDenominator := 3572
  table := BinomialMassData.Q1687_3572.Degree098.table
  base := (64134225074573511611772331078900561429593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31897960000000000000000000000000000000000000000
      center := (200313295)
      previous := (179272429)
      next := (0)
      square := (6211314771420782147404171579992000000000000000)
      linear := (-547889919054672691590617277969450800000000000000)
      constant := (12461758330417180399079871314009998790491740066056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1687_3572.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree098.table
  base := (128268448490940756472065455316720521090723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (22610)
      previous := (20349)
      next := (0)
      square := (702955496991940034789969622000000000000000)
      linear := (-62199415026031247160087645530300000000000000)
      constant := (1418858497063882467060920991064736108113751003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell037.Kernel098
