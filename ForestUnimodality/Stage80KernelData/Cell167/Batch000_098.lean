import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell167.Parameters
import ForestUnimodality.BinomialMassData.Q8069_15194.Batch000_049
import ForestUnimodality.BinomialMassData.Q8069_15194.Batch050_099
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch000_049
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree000.table
  base := (917660896590266384831124909/20000000000000000000000000)
  polynomial :=
    { denominator := 1519400000000000000000000000000000000000000
      center := (8069)
      previous := (0)
      next := (7125)
      square := (304494343906009301486959023684000000000000)
      linear := (-1230822536131448533591736804014000000000000)
      constant := (69714698313962537255620559336730000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree000.table
  base := (917660896590266384831124909/20000000000000000000000000)
  polynomial :=
    { denominator := 2279100000000000000000000000000000000000000
      center := (12116)
      previous := (0)
      next := (10675)
      square := (456741515859013952230438535526000000000000)
      linear := (-1846233804197172800387605206021000000000000)
      constant := (104572047470943805883430839005095000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree001.table
  base := (131817180986031470902543325149366649366057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-295188091699205089084867421555013850000000000000)
      constant := (7748204631999751706208297575404319292472204415313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree001.table
  base := (52686861926740146271773708240497833455343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 346286454000000000000000000000000000000000000000
      center := (1840905040)
      previous := (0)
      next := (1621959500)
      square := (69397305919618579901892831087820440000000000000)
      linear := (-354301833625022609227212645621937620000000000000)
      constant := (9291112317169704390883985349491884650966647411861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49899959490261502531/100000000000000000000)
  directionHi := (12474989872565375633/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree002.table
  base := (160473349949200192830672131142302728241909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-713224426447289630854648461215337500000000000000)
      constant := (9888680683125301102369196648179339759569386966781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree002.table
  base := (160263311111636004370046827526002212219799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-2140434515201633915817662781205222500000000000000)
      constant := (29632022724206309501457591366733040632874832151373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49899959490261502531/100000000000000000000)
  centralHi := (12474989872565375633/25000000000000000000)
  directionLo := (70569199472995851627/100000000000000000000)
  directionHi := (17642299868248962907/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree003.table
  base := (103864494352318868864652618494049543370277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-836072669496169083539562079320647300000000000000)
      constant := (7032922687229568501450801641196349712335405221293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree003.table
  base := (10369346925603487760579372250590836550823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 173143227000000000000000000000000000000000000000
      center := (920452520)
      previous := (0)
      next := (810979750)
      square := (34698652959809289950946415543910220000000000000)
      linear := (-250935986227815478549926233430075690000000000000)
      constant := (2107328415165608317548590616968730937039043725821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70569199472995851627/100000000000000000000)
  centralHi := (17642299868248962907/25000000000000000000)
  directionLo := (43214632566380849001/50000000000000000000)
  directionHi := (86429265132761698003/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree004.table
  base := (71125089767240509086720153093966696012851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-958920912545048536224475697425957100000000000000)
      constant := (5620016338811895522887681063172284326064351870059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree004.table
  base := (70995349866246228333292010979271677771557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-2878285209354675655180861887396291300000000000000)
      constant := (16843898282812942085371839721858168399071547794439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43214632566380849001/50000000000000000000)
  centralHi := (86429265132761698003/100000000000000000000)
  directionLo := (99799918980523005063/100000000000000000000)
  directionHi := (12474989872565375633/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree005.table
  base := (50893199963796492061848294934254277473227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-1081769155593927988909389315531266900000000000000)
      constant := (4994214203252412210212552029683016480089309627843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree005.table
  base := (1587350685242452094825919922222669119689/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-811802639107799131215615360122956425000000000000)
      constant := (3743645156698591448262515292246797051489621571224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99799918980523005063/100000000000000000000)
  centralHi := (12474989872565375633/12500000000000000000)
  directionLo := (111579701494710474771/100000000000000000000)
  directionHi := (27894925373677618693/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree006.table
  base := (18717974536645232066191717289598975074349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-602308699321403720797151466818288350000000000000)
      constant := (2412323368959473455809474072714734843421783594741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree006.table
  base := (7471980962860651144369422570544225816647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 346286454000000000000000000000000000000000000000
      center := (1840905040)
      previous := (0)
      next := (1621959500)
      square := (69397305919618579901892831087820440000000000000)
      linear := (-723227180701543478908812198717472020000000000000)
      constant := (2894533957798874658292513443882091684110971899869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111579701494710474771/100000000000000000000)
  centralHi := (27894925373677618693/25000000000000000000)
  directionLo := (61114719468345827361/50000000000000000000)
  directionHi := (122229438936691654723/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree007.table
  base := (1391297446185109607232100963546631269181/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57714409000000000000000000000000000000000000000
      center := (306500965)
      previous := (0)
      next := (270643125)
      square := (11566217653269763316982138514636740000000000000)
      linear := (-132746564169168689427921655174188650000000000000)
      constant := (494236146454976153459981698997114025283402658058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree007.table
  base := (27764538568989920312521461152037726248067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-3985061250584238264225660546682894500000000000000)
      constant := (14831746077953832383669390033029770748332922892209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61114719468345827361/50000000000000000000)
  centralHi := (122229438936691654723/100000000000000000000)
  directionLo := (26404576648685865981/20000000000000000000)
  directionHi := (66011441621714664953/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree008.table
  base := (4107946480712031497787837324474070651337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (613001930)
      previous := (0)
      next := (541286250)
      square := (23132435306539526633964277029273480000000000000)
      linear := (-290062776948113269392826033969439260000000000000)
      constant := (1051886475835068052452939010878183583466160014833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree008.table
  base := (2048818815379739341687365573411898827853/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 173143227000000000000000000000000000000000000000
      center := (920452520)
      previous := (0)
      next := (810979750)
      square := (34698652959809289950946415543910220000000000000)
      linear := (-435398659766075913390726009977842890000000000000)
      constant := (1578846989313240776785438538846952603251985901631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26404576648685865981/20000000000000000000)
  centralHi := (66011441621714664953/50000000000000000000)
  directionLo := (28227679789198340651/20000000000000000000)
  directionHi := (17642299868248962907/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree009.table
  base := (14761086651593206721142850534016758480587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-1573162127789445799649043787952506100000000000000)
      constant := (5728752238889219484837184471519369611802816678083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree009.table
  base := (3679123552207874470719827197185481733779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-1180727986184320000897214913218490825000000000000)
      constant := (4300460106755091808351595299392063124936050964833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28227679789198340651/20000000000000000000)
  centralHi := (17642299868248962907/12500000000000000000)
  directionLo := (74849939235392253797/50000000000000000000)
  directionHi := (29939975694156901519/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree010.table
  base := (5017004885772255569371060393341566461311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-848005185419162626166978703028907950000000000000)
      constant := (3162001581873028510768816198146069293448785730199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree010.table
  base := (1998928985690979005702141726004226296451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 346286454000000000000000000000000000000000000000
      center := (1840905040)
      previous := (0)
      next := (1621959500)
      square := (69397305919618579901892831087820440000000000000)
      linear := (-1018367458362760174654091841193899540000000000000)
      constant := (3798622019182393033845434511121227956605784787377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74849939235392253797/50000000000000000000)
  centralHi := (29939975694156901519/20000000000000000000)
  directionLo := (157797527139361058859/100000000000000000000)
  directionHi := (7889876356968052943/5000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree011.table
  base := (6089197534370191453385223559559247252389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-1818858613887204705018871024163125700000000000000)
      constant := (7029642419325384744171475618539490555656504973101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree011.table
  base := (60540429491297225096243159381242704493/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17314322700000000000000000000000000000000000000
      center := (92045252)
      previous := (0)
      next := (81097975)
      square := (3469865295980928995094641554391022000000000000)
      linear := (-54607626388903217429520587590650321000000000000)
      constant := (211157730855205639523699625135460329126125418911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157797527139361058859/100000000000000000000)
  centralHi := (7889876356968052943/5000000000000000000)
  directionLo := (20687430335391437619/12500000000000000000)
  directionHi := (165499442683131500953/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree012.table
  base := (1378380186869227885733877307540128853477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-970853428468042078851892321134217750000000000000)
      constant := (3917932464855548492844172533946637480562272650093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree012.table
  base := (545039070183958196748391511181204369663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 346286454000000000000000000000000000000000000000
      center := (1840905040)
      previous := (0)
      next := (1621959500)
      square := (69397305919618579901892831087820440000000000000)
      linear := (-1165937597193368522526731662432113300000000000000)
      constant := (4708096568946951825199014398779002546309952722501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20687430335391437619/12500000000000000000)
  centralHi := (165499442683131500953/100000000000000000000)
  directionLo := (34571706053104679201/20000000000000000000)
  directionHi := (86429265132761698003/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree013.table
  base := (-78124917098804094022608615215530572829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-2064555099984963610388698260373745300000000000000)
      constant := (8736043741386241870206763071597363045367742806939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree013.table
  base := (-106508856719331502681847053842877917117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-6198613333043363482315257865256100900000000000000)
      constant := (26247395256802021254783722405174973766463324083441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34571706053104679201/20000000000000000000)
  centralHi := (86429265132761698003/50000000000000000000)
  directionLo := (89958431292856878733/50000000000000000000)
  directionHi := (179916862585713757467/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree014.table
  base := (-2498114497973635739447227579385755981727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-2187403343033843063073611878479055100000000000000)
      constant := (9725408402935903231442863103241724010496411395657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree014.table
  base := (-126180848525447090507361654839662532641/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86571613500000000000000000000000000000000000000
      center := (460226260)
      previous := (0)
      next := (405489875)
      square := (17349326479904644975473207771955110000000000000)
      linear := (-328376934005994217599842870917581765000000000000)
      constant := (1461110890819394924034197575196988061507544427493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89958431292856878733/50000000000000000000)
  centralHi := (179916862585713757467/100000000000000000000)
  directionLo := (186708552026457389807/100000000000000000000)
  directionHi := (11669284501653586863/6250000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree015.table
  base := (-570727707850981386873212426371458590871/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-1155125793041361257879262748292182450000000000000)
      constant := (5400172612552920200818590225202965261839629759044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree015.table
  base := (-4588688167235846458543100974457912772591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-6936464027196405221678456971447169700000000000000)
      constant := (32454118825745059631817555393189850406869077108843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186708552026457389807/100000000000000000000)
  centralHi := (11669284501653586863/6250000000000000000)
  directionLo := (193261712082207542657/100000000000000000000)
  directionHi := (96630856041103771329/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree016.table
  base := (-6330478146361664254865725502102104458627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-2433099829131601968443439114689674700000000000000)
      constant := (11958012827420322867627893015814789583514077743557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree016.table
  base := (-1587731802562839737227673309650289743969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-1826347343568231522840014131135676025000000000000)
      constant := (8983644703340771738481396369355764192244203552037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193261712082207542657/100000000000000000000)
  centralHi := (96630856041103771329/50000000000000000000)
  directionLo := (99799918980523005063/50000000000000000000)
  directionHi := (199599837961046010127/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree017.table
  base := (-978973057606128741942479605706470687471/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-1277974036090240710564176366397492250000000000000)
      constant := (6598059959139962475701090198330177267187150121444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree017.table
  base := (-981252484952722609668232811479371693851/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-1918578680337361740260414019409559625000000000000)
      constant := (9914181613803822178676188808926698181988363605646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99799918980523005063/50000000000000000000)
  centralHi := (199599837961046010127/100000000000000000000)
  directionLo := (205742803692390570223/100000000000000000000)
  directionHi := (12858925230774410639/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree018.table
  base := (-2275569961792661741482767425697028488579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-1339398157614680436906633175450147150000000000000)
      constant := (7256394257313377096180878724321887825450999530378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree018.table
  base := (-9118495319137600832703166643510804865499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-8043240068425967830723255630733772900000000000000)
      constant := (43614929550374232707974110277957575036220202174727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205742803692390570223/100000000000000000000)
  centralHi := (12858925230774410639/6250000000000000000)
  directionLo := (211707598418987554883/100000000000000000000)
  directionHi := (52926899604746888721/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree019.table
  base := (-2542226270774471255456543572247009183057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-1400822279139120163249089984502802050000000000000)
      constant := (7953231872696867826274035136524090875964584863374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree019.table
  base := (-159113832281779918255374154042619558221/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-2103041353875622175101213795957326825000000000000)
      constant := (11951131262736579590678506667736362566500826893328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211707598418987554883/100000000000000000000)
  centralHi := (52926899604746888721/25000000000000000000)
  directionLo := (54377220176205817633/25000000000000000000)
  directionHi := (217508880704823270533/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree020.table
  base := (-2210820692480494844367456667831618248131/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (613001930)
      previous := (0)
      next := (541286250)
      square := (23132435306539526633964277029273480000000000000)
      linear := (-584898560265423955836618717422182780000000000000)
      constant := (3475170061828964109451583945769777441295503980421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree020.table
  base := (-8853458859521019648273347246637725537/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34628645400000000000000000000000000000000000000
      center := (184090504)
      previous := (0)
      next := (162195950)
      square := (6939730591961857990189283108782044000000000000)
      linear := (-175621815251580191401729094738496834000000000000)
      constant := (1044432573740805207537804746389769562514587802525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54377220176205817633/25000000000000000000)
  centralHi := (217508880704823270533/100000000000000000000)
  directionLo := (111579701494710474771/50000000000000000000)
  directionHi := (223159402989420949543/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree021.table
  base := (-5888320452759331330700749402683599388989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-1523670522187999615934003602608111850000000000000)
      constant := (9459932570936402612151888940104743947271738757499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree021.table
  base := (-1178786592752425831044795524445611137987/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 173143227000000000000000000000000000000000000000
      center := (920452520)
      previous := (0)
      next := (810979750)
      square := (34698652959809289950946415543910220000000000000)
      linear := (-915001610965553043976805429002037610000000000000)
      constant := (5686299303912757693863194034851007541581788535951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111579701494710474771/50000000000000000000)
  centralHi := (223159402989420949543/100000000000000000000)
  directionLo := (57167585384838342203/25000000000000000000)
  directionHi := (228670341539353368813/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree022.table
  base := (-12352243156072251449455984999800158989259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-3170189287424878684552920823321533500000000000000)
      constant := (20537600641578241055531791670716346605828879467069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree022.table
  base := (-96579118107427894583509354177314011873/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-2379735364183012827362413460778977625000000000000)
      constant := (15431474299337379239548613858915143297343758906528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57167585384838342203/25000000000000000000)
  centralHi := (228670341539353368813/100000000000000000000)
  directionLo := (2925644455095915749/1250000000000000000)
  directionHi := (234051556407673259921/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree023.table
  base := (-12794105568195722047715493451214838335059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-3293037530473758137237834441426843300000000000000)
      constant := (22228295246195826165675638089305356573461525834869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree023.table
  base := (-2560558219998965249081790449200384303801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 346286454000000000000000000000000000000000000000
      center := (1840905040)
      previous := (0)
      next := (1621959500)
      square := (69397305919618579901892831087820440000000000000)
      linear := (-1977573360761714435826250679242288980000000000000)
      constant := (13361611689841529070854029166564701171999746494173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2925644455095915749/1250000000000000000)
  centralHi := (234051556407673259921/100000000000000000000)
  directionLo := (239311798735423817811/100000000000000000000)
  directionHi := (59827949683855954453/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree024.table
  base := (-13113308845980789244201276285802755068677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-3415885773522637589922748059532153100000000000000)
      constant := (23991309439437603353948110290073380900639552533107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree024.table
  base := (-6560463516755712508135996515187593109623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4602262600)
      previous := (0)
      next := (4054898750)
      square := (173493264799046449754732077719551100000000000000)
      linear := (-5128396075442546524406426474653489650000000000000)
      constant := (36053780122374187299667549792776313618636909026579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239311798735423817811/100000000000000000000)
  centralHi := (59827949683855954453/25000000000000000000)
  directionLo := (61114719468345827361/25000000000000000000)
  directionHi := (48891775574676661889/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree025.table
  base := (-3329790547763806280165563783281771954511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-1769367008285758521303830838818731450000000000000)
      constant := (12913052973116681958332184787391431902345245502002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree025.table
  base := (-13325832702275260907596798302199653309719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-10625717497961613918494452502402513700000000000000)
      constant := (77622792735650377272600032302823060827674021876787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61114719468345827361/25000000000000000000)
  centralHi := (48891775574676661889/20000000000000000000)
  directionLo := (249499797451307512657/100000000000000000000)
  directionHi := (124749898725653756329/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree026.table
  base := (-13419488630531846001219680599130909764673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-3661582259620396495292575295742772700000000000000)
      constant := (27732233265196700683352205520370908929299568726743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree026.table
  base := (-3356330015546730861848411746637764602843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-2748660711259533697044013013874512025000000000000)
      constant := (20838100833664960902995709350594275636597389605639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249499797451307512657/100000000000000000000)
  centralHi := (124749898725653756329/50000000000000000000)
  directionLo := (50888173433666574777/20000000000000000000)
  directionHi := (127220433584166436943/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree027.table
  base := (-1342086332611802677760463985322832536059/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57714409000000000000000000000000000000000000000
      center := (306500965)
      previous := (0)
      next := (270643125)
      square := (11566217653269763316982138514636740000000000000)
      linear := (-378443050266927594797748891384808250000000000000)
      constant := (2970931191475559308119391944392729835975383625869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree027.table
  base := (-104890263376121460058499048161520060023/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-2840892048028663914464412902148395625000000000000)
      constant := (22323813856484940788017561258829687286636290744928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50888173433666574777/20000000000000000000)
  centralHi := (127220433584166436943/50000000000000000000)
  directionLo := (32410974424785636751/12500000000000000000)
  directionHi := (259287795398285094009/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree028.table
  base := (-833050821420320569402034933437984581521/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-1953639372859077700331201265976696150000000000000)
      constant := (15878511457584029517280916727646987953811225311288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree028.table
  base := (-6666625286283529639741974411921598436061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4602262600)
      previous := (0)
      next := (4054898750)
      square := (173493264799046449754732077719551100000000000000)
      linear := (-5866246769595588263769625580844558450000000000000)
      constant := (47725196896042590534222818495644426375782245291153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32410974424785636751/12500000000000000000)
  centralHi := (259287795398285094009/100000000000000000000)
  directionLo := (26404576648685865981/10000000000000000000)
  directionHi := (264045766486858659811/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree029.table
  base := (-1643498004849890739011075612609888162597/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-2015063494383517426673658075029351050000000000000)
      constant := (16937549063844075329193814428721986928558472959308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree029.table
  base := (-6575923671061776192260779031772741855311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4602262600)
      previous := (0)
      next := (4054898750)
      square := (173493264799046449754732077719551100000000000000)
      linear := (-6050709443133848698610425357392325650000000000000)
      constant := (50908507810063211819053586285196486944533486371403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26404576648685865981/10000000000000000000)
  centralHi := (264045766486858659811/100000000000000000000)
  directionLo := (26871950572439364837/10000000000000000000)
  directionHi := (268719505724393648371/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree030.table
  base := (-12882281598288831975228433253604922320639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-4152975231815914306032229768164011900000000000000)
      constant := (36063312143846462220662726952527754288773411612649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree030.table
  base := (-12885641061533851754761719676130881740043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-12470344233344218266902450267880185700000000000000)
      constant := (108394446163857336718849637021032220261173579861239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26871950572439364837/10000000000000000000)
  centralHi := (268719505724393648371/100000000000000000000)
  directionLo := (2186506674512817229/800000000000000000)
  directionHi := (136656667157051076813/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree031.table
  base := (-3133747269770770923386361199980831300279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-2137911737432396879358571693134660850000000000000)
      constant := (19160737736177172470613710892892151670351391959778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree031.table
  base := (-3134476791881124130846810218718111180653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-3209817395105184784146012455243930025000000000000)
      constant := (28795529575898313252152994080345404526836959612769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2186506674512817229/800000000000000000)
  centralHi := (136656667157051076813/50000000000000000000)
  directionLo := (55566243231307948029/20000000000000000000)
  directionHi := (138915608078269870073/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree032.table
  base := (-12108866607433525518267896645159141624763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-4398671717913673211402057004374631500000000000000)
      constant := (40649428814156419775300945174279747830179503689933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree032.table
  base := (-12111398673437397510079694726159119399409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-13208194927497260006265649374071254500000000000000)
      constant := (122179555373720180013728307798290299951708023847157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55566243231307948029/20000000000000000000)
  centralHi := (138915608078269870073/50000000000000000000)
  directionLo := (282276797891983406511/100000000000000000000)
  directionHi := (17642299868248962907/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree033.table
  base := (-464249381827436789126872682094140581527/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23085763600000000000000000000000000000000000000
      center := (122600386)
      previous := (0)
      next := (108257250)
      square := (4626487061307905326792855405854696000000000000)
      linear := (-180860798438502106563478824899197652000000000000)
      constant := (1721881530036449407972369816137814865974252877457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree033.table
  base := (-2321685901907407179676291888092256977979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 346286454000000000000000000000000000000000000000
      center := (1840905040)
      previous := (0)
      next := (1621959500)
      square := (69397305919618579901892831087820440000000000000)
      linear := (-2715424054914756175189449785433357780000000000000)
      constant := (25877271346577014499719864959428587833119448001767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282276797891983406511/100000000000000000000)
  centralHi := (17642299868248962907/6250000000000000000)
  directionLo := (57330688670303407309/20000000000000000000)
  directionHi := (143326721675758518273/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree034.table
  base := (-5514521783234570594852665006701626400039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-2322184102005716058385942120292625550000000000000)
      constant := (22757095600350431612000157533965064842982951538049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree034.table
  base := (-5515472280347502109287207208899346452599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4602262600)
      previous := (0)
      next := (4054898750)
      square := (173493264799046449754732077719551100000000000000)
      linear := (-6973022810825150872814424240131161650000000000000)
      constant := (68401092818722559725951463749497646037006006603027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57330688670303407309/20000000000000000000)
  centralHi := (143326721675758518273/50000000000000000000)
  directionLo := (58192852668488808399/20000000000000000000)
  directionHi := (72741065835611010499/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree035.table
  base := (-10378933557033591057274156668864100541903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-4767216447060311569456797858690560900000000000000)
      constant := (48050793018401820311734710225888041235907488619673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree035.table
  base := (-32439307902037981056616735553074686373/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 86571613500000000000000000000000000000000000000
      center := (460226260)
      previous := (0)
      next := (405489875)
      square := (17349326479904644975473207771955110000000000000)
      linear := (-715748548436341130765522401667892885000000000000)
      constant := (7221337952493286366641780726177918404469853669264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58192852668488808399/20000000000000000000)
  centralHi := (72741065835611010499/25000000000000000000)
  directionLo := (147606070758912948499/50000000000000000000)
  directionHi := (295212141517825896999/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree036.table
  base := (-4828641568086618020159586382326939898799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-2445032345054595511070855738397935350000000000000)
      constant := (25328382068922588190555688006600512518962295905209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree036.table
  base := (-2414676350988300849086212272867940322247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-3670974078950835871248011896613348025000000000000)
      constant := (38064959768247529030079729486757303867762734528931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147606070758912948499/50000000000000000000)
  centralHi := (295212141517825896999/100000000000000000000)
  directionLo := (299399756941569015189/100000000000000000000)
  directionHi := (29939975694156901519/10000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree037.table
  base := (-8865251280746186833516321211983692858863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-5012912933158070474826625094901180500000000000000)
      constant := (53332037669366520896530510938230792849013201543033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree037.table
  base := (-8866480046543517221448435982186634384947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-15052821662879864354673647139548926500000000000000)
      constant := (160301225750640612338936099286828052806321116196031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299399756941569015189/100000000000000000000)
  centralHi := (29939975694156901519/10000000000000000000)
  directionLo := (3035296038507617179/1000000000000000000)
  directionHi := (303529603850761717901/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree038.table
  base := (-4001906159795133057612544410466108357353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-2567880588103474963755769356503245150000000000000)
      constant := (28038278690076403632631900065095179291625410800623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree038.table
  base := (-4002436567127256046893297920959907919937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4602262600)
      previous := (0)
      next := (4054898750)
      square := (173493264799046449754732077719551100000000000000)
      linear := (-7710873504978192612177623346322230450000000000000)
      constant := (84275375508262553571334131917408351805119250183301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3035296038507617179/1000000000000000000)
  centralHi := (303529603850761717901/100000000000000000000)
  directionLo := (307604009029352674461/100000000000000000000)
  directionHi := (153802004514676337231/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree039.table
  base := (-22105579224638749191762569292779201761/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 57714409000000000000000000000000000000000000000
      center := (306500965)
      previous := (0)
      next := (270643125)
      square := (11566217653269763316982138514636740000000000000)
      linear := (-525860941925582938019645233111180010000000000000)
      constant := (5889027599637901139628208552094966262891908024032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree039.table
  base := (-7074700537232033879754872136147547337099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-15790672357032906094036846245739995300000000000000)
      constant := (177008273608253735817563076336963848305919422321527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307604009029352674461/100000000000000000000)
  centralHi := (153802004514676337231/50000000000000000000)
  directionLo := (155812573568422119069/50000000000000000000)
  directionHi := (311625147136844238139/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree040.table
  base := (-6075858978422437071360429677931388991747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-5381457662304708832881365949217109900000000000000)
      constant := (61773153775857279342970991427298935541792216017477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree040.table
  base := (-6076648007448258442349800579295303784007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-16159597704109426963718445798835529700000000000000)
      constant := (185673674792517114220489806709853109716891717029411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155812573568422119069/50000000000000000000)
  centralHi := (311625147136844238139/100000000000000000000)
  directionLo := (157797527139361058859/50000000000000000000)
  directionHi := (315595054278722117719/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree041.table
  base := (-5010612092629064912542524542616283995287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-5504305905353588285566279567322419700000000000000)
      constant := (64725157308095731320235473154857176655435852009617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree041.table
  base := (-2505645965274663964734583332092673309101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4602262600)
      previous := (0)
      next := (4054898750)
      square := (173493264799046449754732077719551100000000000000)
      linear := (-8264261525592973916700022675965532050000000000000)
      constant := (97273427386022236409930360553551728080205484391073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157797527139361058859/50000000000000000000)
  centralHi := (315595054278722117719/100000000000000000000)
  directionLo := (39939455007376340531/12500000000000000000)
  directionHi := (319515640059010724249/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree042.table
  base := (-1939265679559961307040785733963463455793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-2813577074201233869125596592713864750000000000000)
      constant := (33873129252766847245440483260835383929055809378663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree042.table
  base := (-3879116768074275292875128479392688532961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-16897448398262468703081644905026598500000000000000)
      constant := (203627729665601586063948384140774858107197236594853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39939455007376340531/12500000000000000000)
  centralHi := (319515640059010724249/100000000000000000000)
  directionLo := (323388698317441263121/100000000000000000000)
  directionHi := (161694349158720631561/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree043.table
  base := (-670006476891401104325657951011139773023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-2875001195725673595468053401766519650000000000000)
      constant := (35418216877747013071795296117512628381167166823186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree043.table
  base := (-2680529717898441382384839170538911653773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-17266373745338989572763244458122132900000000000000)
      constant := (212916228969634289894290531555281193907197836054529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323388698317441263121/100000000000000000000)
  centralHi := (161694349158720631561/50000000000000000000)
  directionLo := (81803979180637499963/25000000000000000000)
  directionHi := (327215916722549999853/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree044.table
  base := (-2830879371052563695022225283900945043/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11542881800000000000000000000000000000000000000
      center := (61300193)
      previous := (0)
      next := (54128625)
      square := (2313243530653952663396427702927348000000000000)
      linear := (-117457012690004532872420408432766982000000000000)
      constant := (1479913264144931279736854403603204977423017754130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree044.table
  base := (-1415873036560192998117473673874840032909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-17635299092415510442444844011217667300000000000000)
      constant := (222412293424741069633804865417582476602593349542657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81803979180637499963/25000000000000000000)
  centralHi := (327215916722549999853/100000000000000000000)
  directionLo := (20687430335391437619/6250000000000000000)
  directionHi := (66199777073252600381/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree045.table
  base := (-17012368646740106498255013470479209271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (613001930)
      previous := (0)
      next := (541286250)
      square := (23132435306539526633964277029273480000000000000)
      linear := (-1199139775509821219261186807948731780000000000000)
      constant := (15444786034531314121738289549802484853490136914161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree045.table
  base := (-42717198184096904348608625524475545467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4602262600)
      previous := (0)
      next := (4054898750)
      square := (173493264799046449754732077719551100000000000000)
      linear := (-9002112219746015656063221782156600850000000000000)
      constant := (116057936611205042357424067820615524736575258397991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20687430335391437619/6250000000000000000)
  centralHi := (66199777073252600381/20000000000000000000)
  directionLo := (334739104484131424313/100000000000000000000)
  directionHi := (167369552242065712157/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree046.table
  base := (1310864536127743441497157145820727588301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-6118547120597985548990847657848968700000000000000)
      constant := (80521220622321720750996381963466224412708787529109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree046.table
  base := (327636102321794442600934729135291334363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-4593287446642138045452010779352184025000000000000)
      constant := (60506731624438364436953585079079697861216745809401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334739104484131424313/100000000000000000000)
  centralHi := (167369552242065712157/50000000000000000000)
  directionLo := (67687598281507372039/20000000000000000000)
  directionHi := (84609497851884215049/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree047.table
  base := (2772135097045317984919466126532026855761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-6241395363646865001675761275954278500000000000000)
      constant := (83887522761984371189234691496613018049552374360249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree047.table
  base := (2771860148981963262804529048990792982563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-18742075133645073051489642670504270500000000000000)
      constant := (252145418062626616756988893060659128190289912550801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67687598281507372039/20000000000000000000)
  centralHi := (84609497851884215049/25000000000000000000)
  directionLo := (342096886839237010621/100000000000000000000)
  directionHi := (171048443419618505311/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree048.table
  base := (2149289020804334092172652671947955356799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-3182121803347872227180337447029794150000000000000)
      constant := (43661413338214829177298748867878771522176038416791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree048.table
  base := (429834200324450435691651033440910649039/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 173143227000000000000000000000000000000000000000
      center := (920452520)
      previous := (0)
      next := (810979750)
      square := (34698652959809289950946415543910220000000000000)
      linear := (-1911100048072159392117124222359980490000000000000)
      constant := (26247131834079500438726196476125092823593276908853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342096886839237010621/100000000000000000000)
  centralHi := (171048443419618505311/50000000000000000000)
  directionLo := (34571706053104679201/10000000000000000000)
  directionHi := (345717060531046792011/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree049.table
  base := (2945024471226643889075854294222314520709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-3243545924872311953522794256082449050000000000000)
      constant := (45413562015058798170309215902646698997174838195981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree049.table
  base := (5889846395370805850940464800309187873363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-19479925827798114790852841776695339300000000000000)
      constant := (273004602472924768885601522612261409386143337162401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34571706053104679201/10000000000000000000)
  centralHi := (345717060531046792011/100000000000000000000)
  directionLo := (8732492910795762943/2500000000000000000)
  directionHi := (349299716431830517721/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree050.table
  base := (3773213191051736049752695303331175158829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-3304970046396751679865251065135103950000000000000)
      constant := (47200203907755166290296334372642750755567296867061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree050.table
  base := (1509250529328512855609060098033259611121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 346286454000000000000000000000000000000000000000
      center := (1840905040)
      previous := (0)
      next := (1621959500)
      square := (69397305919618579901892831087820440000000000000)
      linear := (-3969770234974927132106888265958174740000000000000)
      constant := (56749049912862638593159028777680826922398255027467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8732492910795762943/2500000000000000000)
  centralHi := (349299716431830517721/100000000000000000000)
  directionLo := (352845997364979258139/100000000000000000000)
  directionHi := (17642299868248962907/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree051.table
  base := (2316902071763275312019309498174639700971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-3366394167921191406207707874187758850000000000000)
      constant := (49021336070747893403294787435010606968258955982278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree051.table
  base := (2316864831117174875712680766086639194029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-5054444130487789132554010220721602025000000000000)
      constant := (73673310513148533510446871888876264971638860191583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352845997364979258139/100000000000000000000)
  centralHi := (17642299868248962907/5000000000000000000)
  directionLo := (178178494643445038121/50000000000000000000)
  directionHi := (356356989286890076243/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree052.table
  base := (11053508845898909359428152435222830023843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-6855636578891262265100329366480827500000000000000)
      constant := (101753912055519534068573173503969201818133554653787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree052.table
  base := (11053381172940091660302258975358078782807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-20586701869027677399897640435981942500000000000000)
      constant := (305848565176284366281413217532765302440975436098189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178178494643445038121/50000000000000000000)
  centralHi := (356356989286890076243/100000000000000000000)
  directionLo := (359833725171427514933/100000000000000000000)
  directionHi := (179916862585713757467/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree053.table
  base := (12904055918475249587077773285353244287413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-6978484821940141717785242984586137300000000000000)
      constant := (105534123394054548896696136902172388650280667433917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree053.table
  base := (12903946532911873706350066777073189223551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-20955627216104198269579239989077476900000000000000)
      constant := (317211206528088303344179593123363969997347244539077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359833725171427514933/100000000000000000000)
  centralHi := (179916862585713757467/50000000000000000000)
  directionLo := (363277188559750014139/100000000000000000000)
  directionHi := (18163859427987500707/5000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree054.table
  base := (7409594428882106318712752440530367062121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-3550666532494510585235078301345723550000000000000)
      constant := (54691651328447017521831349601974401531543379801489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree054.table
  base := (7409547586770709492145074601135158120541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4602262600)
      previous := (0)
      next := (4054898750)
      square := (173493264799046449754732077719551100000000000000)
      linear := (-10662276281590359569630419771086505650000000000000)
      constant := (164390577839721743960794331528327569140145723725807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363277188559750014139/100000000000000000000)
  centralHi := (18163859427987500707/5000000000000000000)
  directionLo := (183344158405037482083/50000000000000000000)
  directionHi := (366688316810074964167/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree055.table
  base := (4199714169704478264010463454170248189743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-3612090654018950311577535110398378450000000000000)
      constant := (56650723450735928702335382882610566169308674213774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree055.table
  base := (8399388234830692575690505933075917654699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4602262600)
      previous := (0)
      next := (4054898750)
      square := (173493264799046449754732077719551100000000000000)
      linear := (-10846738955128620004471219547634272850000000000000)
      constant := (170279201932472539472702212484026283418720856573673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183344158405037482083/50000000000000000000)
  centralHi := (366688316810074964167/100000000000000000000)
  directionLo := (185034002038906111787/50000000000000000000)
  directionHi := (14802720163112488943/4000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree056.table
  base := (3768603303881423927294723010256934458029/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (613001930)
      previous := (0)
      next := (541286250)
      square := (23132435306539526633964277029273480000000000000)
      linear := (-1469405910217356015167996767780413340000000000000)
      constant := (23457710730803957495623106574179263670396879039861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree056.table
  base := (1177684241864539029662137109950571079719/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-5515600814333440219656009662091020025000000000000)
      constant := (88135735929274897220750149158881564348941687652852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185034002038906111787/50000000000000000000)
  centralHi := (14802720163112488943/4000000000000000000)
  directionLo := (186708552026457389807/50000000000000000000)
  directionHi := (74683420810582955923/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree057.table
  base := (10475816172959259631745204264080963319731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-3734938897067829764262448728503688250000000000000)
      constant := (60672310417439564381509765118577982926148952703979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree057.table
  base := (20951573608718146068977868933734945755703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-22431328604410281748305638201459614500000000000000)
      constant := (364734769043381156390087033174947838870812371073581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186708552026457389807/50000000000000000000)
  centralHi := (74683420810582955923/20000000000000000000)
  directionLo := (376736432478191737891/100000000000000000000)
  directionHi := (94184108119547934473/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree058.table
  base := (11562336932713855838965230956783196701283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-3796363018592269490604905537556343150000000000000)
      constant := (62734823347855826308372894669182676388745297886747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree058.table
  base := (23124623624812809125547140749650281042241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-22800253951486802617987237754555148900000000000000)
      constant := (377133874638843772909906698987792579181110530051707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376736432478191737891/100000000000000000000)
  centralHi := (94184108119547934473/25000000000000000000)
  directionLo := (190013384734816024427/50000000000000000000)
  directionHi := (76005353893926409771/20000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree059.table
  base := (12681057805550055057051957283258557827687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-3857787140116709216947362346608998050000000000000)
      constant := (64831814883357025881676649195168951009217279041983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree059.table
  base := (634051816269444377198517406406935082359/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86571613500000000000000000000000000000000000000
      center := (460226260)
      previous := (0)
      next := (405489875)
      square := (17349326479904644975473207771955110000000000000)
      linear := (-1158458964928166174383441865382534165000000000000)
      constant := (19487012806430942711618958748591162130678296064986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190013384734816024427/50000000000000000000)
  centralHi := (76005353893926409771/20000000000000000000)
  directionLo := (383288861657437940871/100000000000000000000)
  directionHi := (47911107707179742609/12500000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree060.table
  base := (13831968086652611865915149090947474212697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-3919211261641148943289819155661652950000000000000)
      constant := (66963284406121077757810564105750215224228547651073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree060.table
  base := (27663899448852005930487915355388919248701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-23538104645639844357350436860746217700000000000000)
      constant := (402553909835531919978870141124141681318762506698127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383288861657437940871/100000000000000000000)
  centralHi := (47911107707179742609/12500000000000000000)
  directionLo := (77304684832883017063/20000000000000000000)
  directionHi := (96630856041103771329/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree061.table
  base := (6006023510645866326188860443308066379627/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (613001930)
      previous := (0)
      next := (541286250)
      square := (23132435306539526633964277029273480000000000000)
      linear := (-1592254153266235467852910385885723140000000000000)
      constant := (27651692558701013454141057980310603016032941945443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree061.table
  base := (3753760771025416025625665642563077959687/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-5976757498179091306758009103460438025000000000000)
      constant := (103893708167208070750784348414413210837985566179898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77304684832883017063/20000000000000000000)
  centralHi := (96630856041103771329/25000000000000000000)
  directionLo := (7794622848731401667/2000000000000000000)
  directionHi := (389731142436570083351/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree062.table
  base := (32460644619470160381125801031149680203143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-8084119009380056791949465547533925500000000000000)
      constant := (142659310837202847476318454728417502283463398187487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree062.table
  base := (8115154451192910710798253300624535496751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-6068988834948221524178408991734321625000000000000)
      constant := (107200755507667139912638948083505810991283516155477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7794622848731401667/2000000000000000000)
  centralHi := (389731142436570083351/100000000000000000000)
  directionLo := (12278521060599670833/3125000000000000000)
  directionHi := (392912673939189466657/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree063.table
  base := (1747775232560325976553808929165233662219/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57714409000000000000000000000000000000000000000
      center := (306500965)
      previous := (0)
      next := (270643125)
      square := (11566217653269763316982138514636740000000000000)
      linear := (-820696725242893624463437916563923530000000000000)
      constant := (14712911220916081913088747978468779978323750427142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree063.table
  base := (6991096349451683026009469271658542968019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 346286454000000000000000000000000000000000000000
      center := (1840905040)
      previous := (0)
      next := (1621959500)
      square := (69397305919618579901892831087820440000000000000)
      linear := (-4928976137373881393279047104006564180000000000000)
      constant := (88447695147495964992039616557442138251600967457313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12278521060599670833/3125000000000000000)
  centralHi := (392912673939189466657/100000000000000000000)
  directionLo := (79213729946057597943/20000000000000000000)
  directionHi := (99017162432571997429/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree064.table
  base := (37514686954149813037219600347851678127427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-8329815495477815697319292783744545100000000000000)
      constant := (151667866292164436238317647534062870022782675995643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree064.table
  base := (2344666712220217819300832824125568287521/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-6253451508486481959019208768282088825000000000000)
      constant := (113970297988480901246213880992231969386040999081068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79213729946057597943/20000000000000000000)
  centralHi := (99017162432571997429/25000000000000000000)
  directionLo := (99799918980523005063/25000000000000000000)
  directionHi := (399199675922092020253/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree065.table
  base := (40138182537681852527448826737574024216343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-8452663738526695150004206401849854900000000000000)
      constant := (156275572567325483512062116559145098901397924386287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree065.table
  base := (20069082919920692252014271880514249307071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4602262600)
      previous := (0)
      next := (4054898750)
      square := (173493264799046449754732077719551100000000000000)
      linear := (-12691365690511224352879217313111944850000000000000)
      constant := (234865584568670640231614215000101194544508786858117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99799918980523005063/25000000000000000000)
  centralHi := (399199675922092020253/100000000000000000000)
  directionLo := (40230633504014454489/10000000000000000000)
  directionHi := (402306335040144544891/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree066.table
  base := (21412991921715400141494847137454942720511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-4287755990787787301344560009977582350000000000000)
      constant := (80476115299208498667968963905178810433243144542999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree066.table
  base := (42825969591311039153819501435239078528953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-25751656728098969575440034179319424100000000000000)
      constant := (483788405991080352731163702613033547973009335351331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40230633504014454489/10000000000000000000)
  centralHi := (402306335040144544891/100000000000000000000)
  directionLo := (405389187288663106793/100000000000000000000)
  directionHi := (202694593644331553397/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree067.table
  base := (45578084517090144506412932760724399038357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-8698360224624454055374033638060474500000000000000)
      constant := (165697840018703932776704923238856055002378942586013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree067.table
  base := (1823122894210428324000395251328783298079/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 69257290800000000000000000000000000000000000000
      center := (368181008)
      previous := (0)
      next := (324391900)
      square := (13879461183923715980378566217564088000000000000)
      linear := (-1044823283007019617804865349296598340000000000000)
      constant := (19922116057010441746138184890399168026213100960933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405389187288663106793/100000000000000000000)
  centralHi := (202694593644331553397/50000000000000000000)
  directionLo := (408448771729934955419/100000000000000000000)
  directionHi := (20422438586496747771/5000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree068.table
  base := (24197239608295624466418348379858739211163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-4410604233836666754029473628082892150000000000000)
      constant := (85256200259935977827449739840256354537057398747667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree068.table
  base := (48394468840791105676892316826434758603279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-26489507422252011314803233285510492900000000000000)
      constant := (512524654523799977177945772271274127409537738841333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408448771729934955419/100000000000000000000)
  centralHi := (20422438586496747771/5000000000000000000)
  directionLo := (411485607384781140447/100000000000000000000)
  directionHi := (12858925230774410639/3125000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree069.table
  base := (51275163450837644397163537747303588723673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-8944056710722212960743860874271094100000000000000)
      constant := (175395911842720087490671274466323206966765851504257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree069.table
  base := (51275154600693244113136289758944794227143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-26858432769328532184484832838606027300000000000000)
      constant := (527203664516693038018505448623845335787338510010461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411485607384781140447/100000000000000000000)
  centralHi := (12858925230774410639/3125000000000000000)
  directionLo := (414500194260451451501/100000000000000000000)
  directionHi := (207250097130225725751/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree070.table
  base := (54220133444131982279297191366690624863779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-9066904953771092413428774492376403900000000000000)
      constant := (180348373769336187245544486175827527199853710491611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree070.table
  base := (1694378934278022340807856043777889029797/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-6806839529101263263541608097925390425000000000000)
      constant := (135522482689179663223433741869449996822935613879352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414500194260451451501/100000000000000000000)
  centralHi := (207250097130225725751/50000000000000000000)
  directionLo := (104373253577928709159/25000000000000000000)
  directionHi := (417493014311714836637/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree071.table
  base := (7153673252775288692510989649020034843731/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4064395000000000000000000000000000000000000000
      center := (21584575)
      previous := (0)
      next := (19059375)
      square := (814522369948574881477615388354700000000000000)
      linear := (-64716571808591351169814705003392350000000000000)
      constant := (1305421028989570599609780518858112177614948846196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree071.table
  base := (14307344896844178307767687774464734571071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6096592500000000000000000000000000000000000000
      center := (32410300)
      previous := (0)
      next := (28555625)
      square := (1221783554922862322216423082532050000000000000)
      linear := (-97170012195357654661436732199989775000000000000)
      constant := (1961913565844565168247773017141130456920192870227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104373253577928709159/25000000000000000000)
  centralHi := (417493014311714836637/100000000000000000000)
  directionLo := (420464532340376443791/100000000000000000000)
  directionHi := (26279033271273527737/6250000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree072.table
  base := (6030291851638647430371563846825164966167/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57714409000000000000000000000000000000000000000
      center := (306500965)
      previous := (0)
      next := (270643125)
      square := (11566217653269763316982138514636740000000000000)
      linear := (-931260143986885131879860172858702350000000000000)
      constant := (19046014873024834227162311985212034962349833400303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree072.table
  base := (15075728257774370112868562960726037949093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-6991302202639523698382407874473157625000000000000)
      constant := (143121057472207287202886107535737173273430423743111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420464532340376443791/100000000000000000000)
  centralHi := (26279033271273527737/6250000000000000000)
  directionLo := (211707598418987554883/50000000000000000000)
  directionHi := (423415196837975109767/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree073.table
  base := (7930091085385215003808945972037711685881/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-4717724841458865385741757673346166650000000000000)
      constant := (97809730740517965751093583500329007622652062237316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree073.table
  base := (3965045250507227889874191452163992700937/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-7083533539408653915802807762747041225000000000000)
      constant := (146998065484817104271308394723984908417778712414796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211707598418987554883/50000000000000000000)
  centralHi := (423415196837975109767/100000000000000000000)
  directionLo := (26646590048499210067/6250000000000000000)
  directionHi := (426345440775987361073/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree074.table
  base := (66642814636027428586252183408063083008969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-9558297925966610224168428964797643100000000000000)
      constant := (200847724260017376040696507623254761170580587534321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree074.table
  base := (66642810652425710804402285274052750553/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17314322700000000000000000000000000000000000000
      center := (92045252)
      previous := (0)
      next := (81097975)
      square := (3469865295980928995094641554391022000000000000)
      linear := (-287030595047111365328928306040836993000000000000)
      constant := (6037075485280880987707033103715667085989724545310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26646590048499210067/6250000000000000000)
  centralHi := (426345440775987361073/100000000000000000000)
  directionLo := (429255682347480037847/100000000000000000000)
  directionHi := (53656960293435004731/12500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree075.table
  base := (8738646848672055501441828694036198023763/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-4840573084507744838426671291451476450000000000000)
      constant := (103072468487833222258308226087386147724193798004268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree075.table
  base := (349545856977577509766803556676544369153/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17314322700000000000000000000000000000000000000
      center := (92045252)
      previous := (0)
      next := (81097975)
      square := (3469865295980928995094641554391022000000000000)
      linear := (-290719848517876574025744301571792337000000000000)
      constant := (6196300893837109347849231706564649474567659353462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429255682347480037847/100000000000000000000)
  centralHi := (53656960293435004731/12500000000000000000)
  directionLo := (432146325663808490013/100000000000000000000)
  directionHi := (216073162831904245007/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree076.table
  base := (36619903904918074241357010858235955898403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-4901997206032184564769128100504131350000000000000)
      constant := (105755549775516470734097389248606089877226393188827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree076.table
  base := (36619902459461769834830414617045417533329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4602262600)
      previous := (0)
      next := (4054898750)
      square := (173493264799046449754732077719551100000000000000)
      linear := (-14720455099432089136128014855137384050000000000000)
      constant := (317879942138927124901432580437882291997282963112683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432146325663808490013/100000000000000000000)
  centralHi := (216073162831904245007/50000000000000000000)
  directionLo := (54377220176205817633/12500000000000000000)
  directionHi := (87003552281929308213/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree077.table
  base := (76634712576434304928921544514489942976059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-9926842655113248582223169819113572500000000000000)
      constant := (216946211921420616727478401794034384395306946334131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree077.table
  base := (76634710114362650535130181192807963146023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-29809835545940699141937629263370302500000000000000)
      constant := (652096933018625626176198281247332321130399494436221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54377220176205817633/12500000000000000000)
  centralHi := (87003552281929308213/20000000000000000000)
  directionLo := (684172449155240989/156250000000000000)
  directionHi := (437870367459354232961/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree078.table
  base := (16018777629338979036512866077182496669853/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (613001930)
      previous := (0)
      next := (541286250)
      square := (23132435306539526633964277029273480000000000000)
      linear := (-2009938179632425606981616687443776460000000000000)
      constant := (44490054806487004781850287352274670240445034011877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree078.table
  base := (125146696953442404334532598404181605671/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 86571613500000000000000000000000000000000000000
      center := (460226260)
      previous := (0)
      next := (405489875)
      square := (17349326479904644975473207771955110000000000000)
      linear := (-1508938044650861000580961440823291845000000000000)
      constant := (33432061772235984600464756137598848631997390090144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (684172449155240989/156250000000000000)
  centralHi := (437870367459354232961/100000000000000000000)
  directionLo := (55088063682179548867/12500000000000000000)
  directionHi := (440704509457436390937/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree079.table
  base := (83617333728202719286104997467024232865317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-10172539141211007487592997055324192100000000000000)
      constant := (228023285838342388065347788309557433088500147252653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree079.table
  base := (20904332985825317264799557373699150644761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-7636921560023435220325207092390342825000000000000)
      constant := (171348197855135103440685034474910428369793050183747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55088063682179548867/12500000000000000000)
  centralHi := (440704509457436390937/100000000000000000000)
  directionLo := (221760270682808161753/50000000000000000000)
  directionHi := (443520541365616323507/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree080.table
  base := (17441009730939644824666617853198326713253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (613001930)
      previous := (0)
      next := (541286250)
      square := (23132435306539526633964277029273480000000000000)
      linear := (-2059077476851977388055582134685900380000000000000)
      constant := (46733049460137986569412252324508048586044309362477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree080.table
  base := (87205047135320572071111256682219866702033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-30916611587170261750982427922656905700000000000000)
      constant := (702351600832101290686801322568085437244299841080491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221760270682808161753/50000000000000000000)
  centralHi := (443520541365616323507/100000000000000000000)
  directionLo := (111579701494710474771/25000000000000000000)
  directionHi := (89263761195768379817/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree081.table
  base := (709820565359225081119359702808543898153/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-5209117813654383196481412145767405850000000000000)
      constant := (119688079193573005871856691696431012478877221540928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree081.table
  base := (11357128884103680271729467964523869570059/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-7821384233561695655166006868938110025000000000000)
      constant := (179879415895894847164467380510238497691774235680786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111579701494710474771/25000000000000000000)
  centralHi := (89263761195768379817/20000000000000000000)
  directionLo := (449099635412353522783/100000000000000000000)
  directionHi := (14034363606636047587/3125000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree082.table
  base := (94573284391013855835333660407337019649199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-10541083870357645845647737909640121500000000000000)
      constant := (245156019070525024485908455356267858252874907608391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree082.table
  base := (47286641645286385865296402455430816187349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4602262600)
      previous := (0)
      next := (4054898750)
      square := (173493264799046449754732077719551100000000000000)
      linear := (-15827231140661651745172813514423987250000000000000)
      constant := (368445489797209468480740248082567750789921442435223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449099635412353522783/100000000000000000000)
  centralHi := (14034363606636047587/3125000000000000000)
  directionLo := (451863351561773149857/100000000000000000000)
  directionHi := (225931675780886574929/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree083.table
  base := (98353804333721361867587393743274206085197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-10663932113406525298332651527745431300000000000000)
      constant := (251004829327967678894675124279829822829151348503573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree083.table
  base := (9835380339741141667292530612686540024797/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 173143227000000000000000000000000000000000000000
      center := (920452520)
      previous := (0)
      next := (810979750)
      square := (34698652959809289950946415543910220000000000000)
      linear := (-3202338762839982436002722658194350890000000000000)
      constant := (75447154879689684198760366782456818719358012599919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451863351561773149857/100000000000000000000)
  centralHi := (225931675780886574929/50000000000000000000)
  directionLo := (454610266538018624517/100000000000000000000)
  directionHi := (227305133269009312259/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree084.table
  base := (10219859186104739795189386735407790627419/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57714409000000000000000000000000000000000000000
      center := (306500965)
      previous := (0)
      next := (270643125)
      square := (11566217653269763316982138514636740000000000000)
      linear := (-1078678035645540475101756514585074110000000000000)
      constant := (25692258914025184877563642200166190310057226780371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree084.table
  base := (102198591064504019557519681214032245208149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-32392312975476345229708826135039043300000000000000)
      constant := (772259371134076449937443256603133644617394204556823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454610266538018624517/100000000000000000000)
  centralHi := (227305133269009312259/50000000000000000000)
  directionLo := (3658725464629653901/800000000000000000)
  directionHi := (228670341539353368813/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree085.table
  base := (26526911673229459718067629400909431035381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-5454814299752142101851239381978025450000000000000)
      constant := (131454649245606610757879958753600548249466545009658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree085.table
  base := (53053823007686786277414302082055642941661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4602262600)
      previous := (0)
      next := (4054898750)
      square := (173493264799046449754732077719551100000000000000)
      linear := (-16380619161276433049695212844067288850000000000000)
      constant := (395127223279043819742043586263271143812478958280047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3658725464629653901/800000000000000000)
  centralHi := (228670341539353368813/50000000000000000000)
  directionLo := (460054894937580046049/100000000000000000000)
  directionHi := (9201097898751600921/2000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree086.table
  base := (110080968593801324984819897225018530911781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-11032476842553163656387392382061360700000000000000)
      constant := (268964957367258243892231619170827576825621671552429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree086.table
  base := (110080968017558137035109185926124747623229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-33130163669629386969072025241230112100000000000000)
      constant := (808456775028681200418505773604204856808046449219983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460054894937580046049/100000000000000000000)
  centralHi := (9201097898751600921/2000000000000000000)
  directionLo := (57844148406671929929/12500000000000000000)
  directionHi := (462753187253375439433/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree087.table
  base := (114118557365614660620635322802572358922159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-11155325085602043109072306000166670500000000000000)
      constant := (275089565756954661334189218083057120274928283689031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree087.table
  base := (14264819609449134323359406698387679677307/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-8374772254176476959688406198581411625000000000000)
      constant := (206716589128003438620436547498022382412742505299378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57844148406671929929/12500000000000000000)
  centralHi := (462753187253375439433/100000000000000000000)
  directionLo := (23271791844972278169/5000000000000000000)
  directionHi := (465435836899445563381/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree088.table
  base := (118220412841758457866439256734554779505391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-11278173328650922561757219618271980300000000000000)
      constant := (281283123650687288628456157908229769777278953878919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree088.table
  base := (118220412425112437096379720929218998792347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-33868014363782428708435224347421180900000000000000)
      constant := (845483190979626451008479688120595318440616062483769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23271791844972278169/5000000000000000000)
  centralHi := (465435836899445563381/100000000000000000000)
  directionLo := (468103112815346519841/100000000000000000000)
  directionHi := (234051556407673259921/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree089.table
  base := (30596633720525739490597206977724880842417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-5700510785849901007221066618188645050000000000000)
      constant := (143772815520184309782447767203682438324831038573106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree089.table
  base := (61193267263945515125528321919360060152017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (4602262600)
      previous := (0)
      next := (4054898750)
      square := (173493264799046449754732077719551100000000000000)
      linear := (-17118469855429474789058411950258357650000000000000)
      constant := (432153639203793266901363276887782313589634333938859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468103112815346519841/100000000000000000000)
  centralHi := (234051556407673259921/50000000000000000000)
  directionLo := (11768881908037897013/2500000000000000000)
  directionHi := (470755276321515880521/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree090.table
  base := (126616923368772650781544827050903832228949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-11523869814748681467127046854482599900000000000000)
      constant := (293877087919195538740957536137899366092928944226141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree090.table
  base := (25323384613535426071927616224014196429751/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 346286454000000000000000000000000000000000000000
      center := (1840905040)
      previous := (0)
      next := (1621959500)
      square := (69397305919618579901892831087820440000000000000)
      linear := (-6921173011587094089559684690722449940000000000000)
      constant := (176667723755153160856053660779351298463658966946477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11768881908037897013/2500000000000000000)
  centralHi := (470755276321515880521/100000000000000000000)
  directionLo := (473392581418083176577/100000000000000000000)
  directionHi := (236696290709041588289/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree091.table
  base := (65455789101301215243341472648437973248431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-5823359028898780459905980236293954850000000000000)
      constant := (150138747140722395339912155956839046549191005342279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree091.table
  base := (130911577946689760113565902776302964677583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-34974790405011991317480023006707784100000000000000)
      constant := (902577212067234148490687409139410266833943735180341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473392581418083176577/100000000000000000000)
  centralHi := (236696290709041588289/50000000000000000000)
  directionLo := (476015275068779960083/100000000000000000000)
  directionHi := (119003818767194990021/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree092.table
  base := (67635249650079150341382266698764968380993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-5884783150423220186248437045346609750000000000000)
      constant := (153373425061150515794524037780502398880012697828137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree092.table
  base := (27054099816534907774850176959871581287039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 346286454000000000000000000000000000000000000000
      center := (1840905040)
      previous := (0)
      next := (1621959500)
      square := (69397305919618579901892831087820440000000000000)
      linear := (-7068743150417702437432324511960663700000000000000)
      constant := (184404611653549955507066442106268977329630745734853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476015275068779960083/100000000000000000000)
  centralHi := (119003818767194990021/25000000000000000000)
  directionLo := (478623597470847635623/100000000000000000000)
  directionHi := (59827949683855954453/12500000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree093.table
  base := (34923421647808171842144739861968011114007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-5946207271947659912590893854399264650000000000000)
      constant := (156642577718856136413912595087483110576700691253726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree093.table
  base := (139693686406429025813910511281372017410977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-35712641099165033056843222112898852900000000000000)
      constant := (941676157365330757493003892014093980482036743002779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478623597470847635623/100000000000000000000)
  centralHi := (59827949683855954453/12500000000000000000)
  directionLo := (481217782311777965551/100000000000000000000)
  directionHi := (30076111394486122847/6250000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree094.table
  base := (72090570008369373689516446354699169834553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-6007631393472099638933350663451919550000000000000)
      constant := (159946205112134176081603302371074037709791854174177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree094.table
  base := (144181139859722681264423630507281968204859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-36081566446241553926524821665994387300000000000000)
      constant := (961536509349894864815612448352754898973900684339993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481217782311777965551/100000000000000000000)
  centralHi := (30076111394486122847/6250000000000000000)
  directionLo := (483798057013662948843/100000000000000000000)
  directionHi := (120949514253415737211/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree095.table
  base := (148732859526940106448202175597248771220839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-12138111029993078730551614945009148900000000000000)
      constant := (326568614479098764148631697668717295356986931369151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree095.table
  base := (232395092802419551348347142190588479909/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 86571613500000000000000000000000000000000000000
      center := (460226260)
      previous := (0)
      next := (405489875)
      square := (17349326479904644975473207771955110000000000000)
      linear := (-1822524589665903739810321060954496085000000000000)
      constant := (49080205710647843534994500477070012530095005642976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483798057013662948843/100000000000000000000)
  centralHi := (120949514253415737211/25000000000000000000)
  directionLo := (97272928593175440427/20000000000000000000)
  directionHi := (60795580370734650267/12500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree096.table
  base := (153348845079962588231170741141641399634101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (3065009650)
      previous := (0)
      next := (2706431250)
      square := (115662176532697633169821385146367400000000000000)
      linear := (-12260959273041958183236528563114458700000000000000)
      constant := (333313768199786765443991857994908495469814955461309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree096.table
  base := (30669768993330701976573907981341242281947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 346286454000000000000000000000000000000000000000
      center := (1840905040)
      previous := (0)
      next := (1621959500)
      square := (69397305919618579901892831087820440000000000000)
      linear := (-7363883428078919133177604154437091220000000000000)
      constant := (200375794389474819149033605353052188556885147422969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97272928593175440427/20000000000000000000)
  centralHi := (60795580370734650267/12500000000000000000)
  directionLo := (61114719468345827361/12500000000000000000)
  directionHi := (488917755746766618889/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree097.table
  base := (2469204635008484521420723649192918447967/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-6191903758045418817960721090609884250000000000000)
      constant := (170063935692148581131189243108756358886707605008096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree097.table
  base := (19753637068037925653916985220970810527031/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (2301131300)
      previous := (0)
      next := (2027449375)
      square := (86746632399523224877366038859775550000000000000)
      linear := (-9297085621867779133892405081320247625000000000000)
      constant := (255590270636783134214876776140014768714911436138074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell167.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61114719468345827361/12500000000000000000)
  centralHi := (488917755746766618889/100000000000000000000)
  directionLo := (245728802667485788051/50000000000000000000)
  directionHi := (491457605334971576103/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 8069
  qDenominator := 15194
  table := BinomialMassData.Q8069_15194.Degree098.table
  base := (20346701772372159130111155954424239000533/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (1532504825)
      previous := (0)
      next := (1353215625)
      square := (57831088266348816584910692573183700000000000000)
      linear := (-6253327879569858544303177899662539150000000000000)
      constant := (173505462015457800105283381311711404206762051119988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q8069_15194.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree098.table
  base := (162773614097244395266884175780956862012141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (9204525200)
      previous := (0)
      next := (8109797500)
      square := (346986529598092899509464155439102200000000000000)
      linear := (-37557267834547637405251219878376524900000000000000)
      constant := (1043050446007167096078401023361949222636575805919007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell167.Kernel098
