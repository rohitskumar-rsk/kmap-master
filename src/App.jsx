import React, { useState, useEffect, useMemo, useCallback } from 'react';
import { motion, AnimatePresence } from 'framer-motion';
import { FaYoutube } from "react-icons/fa";
import {
  BookOpen,
  Brain,
  CheckCircle,
  ChevronRight,
  Play,
  Settings,
  RotateCcw,
  XCircle,
  AlertCircle,
  Lightbulb,
  MousePointerClick,
  Check,
  Plus,
  Trash2,
  ArrowRight,
  ArrowLeft,
  AlertTriangle,
  Info
} from 'lucide-react';
import logo from "./assets/logo.png";

// Gray Code mappings for K-Maps
const GRAY_2 = [0, 1];
const GRAY_4 = [0, 1, 3, 2];

// K-Map Layouts: [Row Vars, Col Vars]
const LAYOUTS = {
  2: { rows: 2, cols: 2, rowVars: ['A'], colVars: ['B'] },
  3: { rows: 2, cols: 4, rowVars: ['A'], colVars: ['B', 'C'] },
  4: { rows: 4, cols: 4, rowVars: ['A', 'B'], colVars: ['C', 'D'] }
};

// Generate binary string with padding
const toBin = (num, bits) => num.toString(2).padStart(bits, '0');

// Map integer values (Gray code) to their visual index on the grid
const GRAY_TO_VISUAL = {
  1: { 0: 0, 1: 1 },
  2: { 0: 0, 1: 1, 3: 2, 2: 3 }
};

// Get visual coordinates (r, c) for a minterm
const getGridCoords = (minterm, vars) => {
  const rowBits = vars >= 4 ? 2 : 1;
  const colBits = vars >= 3 ? 2 : 1;

  const colMask = (1 << colBits) - 1;
  const rowGray = minterm >> colBits;
  const colGray = minterm & colMask;

  return {
    r: GRAY_TO_VISUAL[rowBits][rowGray],
    c: GRAY_TO_VISUAL[colBits][colGray]
  };
};

// Map visual (r, c) back to minterm integer
const visualToMinterm = (r, c, vars) => {
  const VISUAL_TO_GRAY = {
    1: { 0: 0, 1: 1 },
    2: { 0: 0, 1: 1, 2: 3, 3: 2 }
  };
  const rowBits = vars >= 4 ? 2 : 1;
  const colBits = vars >= 3 ? 2 : 1;
  const rowGray = VISUAL_TO_GRAY[rowBits][r];
  const colGray = VISUAL_TO_GRAY[colBits][c];
  return (rowGray << colBits) | colGray;
};

// Generate all valid K-Map power-of-2 boxes (handles all wrap-arounds naturally)
const getAllValidBoxes = (vars) => {
  const maxRows = vars === 4 ? 4 : 2;
  const maxCols = vars >= 3 ? 4 : 2;
  const shapes = [];
  
  const dimR = [1, 2, 4].filter(d => d <= maxRows);
  const dimC = [1, 2, 4].filter(d => d <= maxCols);

  for (let r of dimR) {
    for (let c of dimC) {
       const startRows = r === maxRows ? [0] : Array.from({length: maxRows}, (_, i) => i);
       const startCols = c === maxCols ? [0] : Array.from({length: maxCols}, (_, i) => i);

       for (let sr of startRows) {
         for (let sc of startCols) {
           const box = [];
           for (let i = 0; i < r; i++) {
             for (let j = 0; j < c; j++) {
               const curR = (sr + i) % maxRows;
               const curC = (sc + j) % maxCols;
               box.push(visualToMinterm(curR, curC, vars));
             }
           }
           box.sort((a,b)=>a-b);
           shapes.push(box);
         }
       }
    }
  }
  return shapes;
};

// Computes all Prime Implicants (PIs) for the current grid
const getPrimeImplicants = (minterms, dontcares, vars) => {
  const allBoxes = getAllValidBoxes(vars);
  
  // Keep only boxes containing valid 1s or Xs (no 0s)
  const validBoxes = allBoxes.filter(box => {
    return box.every(m => minterms.includes(m) || dontcares.includes(m));
  });

  const PIs = [];
  for (let i = 0; i < validBoxes.length; i++) {
     const box = validBoxes[i];
     let isMaximal = true;
     for (let j = 0; j < validBoxes.length; j++) {
        if (i === j) continue;
        const otherBox = validBoxes[j];
        if (otherBox.length > box.length) {
           // Check if current box is completely contained in a larger box
           if (box.every(m => otherBox.includes(m))) {
             isMaximal = false;
             break;
           }
        }
     }
     if (isMaximal) PIs.push(box);
  }
  
  // Deduplicate PIs (wrap-around can sometimes generate same shape from different origin)
  const uniquePIs = [];
  const seen = new Set();
  for (let p of PIs) {
    const key = p.join(',');
    if (!seen.has(key)) {
      seen.add(key);
      uniquePIs.push(p);
    }
  }
  return uniquePIs;
};

// Computes Minimal Cover sets using a branch-and-bound optimization (Petrick's Method equivalent)
const getMinimumCovers = (PIs, minterms, vars) => {
   const EPIs = [];
   const uncoveredMinterms = new Set(minterms);
   
   // Identify Essential Prime Implicants (EPIs)
   minterms.forEach(m => {
     const coveringPIs = PIs.filter(pi => pi.includes(m));
     if (coveringPIs.length === 1) {
       const epi = coveringPIs[0];
       if (!EPIs.some(e => e.join(',') === epi.join(','))) {
         EPIs.push(epi);
       }
     }
   });

   EPIs.forEach(epi => {
     epi.forEach(m => uncoveredMinterms.delete(m));
   });

   const remainingMinterms = Array.from(uncoveredMinterms);
   if (remainingMinterms.length === 0) return [EPIs]; 

   const remainingPIs = PIs.filter(pi => !EPIs.some(e => e.join(',') === pi.join(',')));
   let minSize = Infinity;
   let minimalCovers = [];

   const search = (idx, currentCover, coveredSet) => {
     if (coveredSet.size === remainingMinterms.length) {
        if (currentCover.length < minSize) {
          minSize = currentCover.length;
          minimalCovers = [[...currentCover]];
        } else if (currentCover.length === minSize) {
          minimalCovers.push([...currentCover]);
        }
        return;
     }
     
     if (idx >= remainingPIs.length) return;
     if (currentCover.length >= minSize) return; // Branch and bound

     const pi = remainingPIs[idx];
     const newCovered = new Set(coveredSet);
     let addedAny = false;
     
     pi.forEach(m => {
       if (remainingMinterms.includes(m) && !newCovered.has(m)) {
         newCovered.add(m);
         addedAny = true;
       }
     });

     // Try path including this PI
     if (addedAny) {
       currentCover.push(pi);
       search(idx + 1, currentCover, newCovered);
       currentCover.pop();
     }

     // Try path excluding this PI
     search(idx + 1, currentCover, coveredSet);
   };

   search(0, [], new Set());
   
   let allCovers = minimalCovers.length === 0 ? [[...EPIs]] : minimalCovers.map(mc => [...EPIs, ...mc]);
   
   // Deduplicate covers
   const uniqueCovers = [];
   const seenCovers = new Set();
   allCovers.forEach(cover => {
     const sig = [...cover].map(pi => pi.slice().sort((a,b)=>a-b).join('-')).sort().join('|');
     if (!seenCovers.has(sig)) {
       seenCovers.add(sig);
       uniqueCovers.push(cover);
     }
   });
   
   // Filter by minimum literal count
   const getCoverLiteralCount = (cover) => cover.reduce((sum, pi) => sum + (vars - Math.log2(pi.length)), 0);
   
   if (uniqueCovers.length === 0) return [];
   
   let minLits = Infinity;
   uniqueCovers.forEach(cover => {
      const lits = getCoverLiteralCount(cover);
      if (lits < minLits) minLits = lits;
   });
   
   return uniqueCovers.filter(cover => getCoverLiteralCount(cover) === minLits);
};

// Translates a valid grouping array into a SOP Boolean term (e.g. A'B)
const groupToTerm = (pi, vars) => {
   if (pi.length === Math.pow(2, vars)) return '1';
   const varNames = LAYOUTS[vars].rowVars.concat(LAYOUTS[vars].colVars);
   let term = '';
   
   for (let i = 0; i < vars; i++) {
      let bitVal = null;
      let isConstant = true;
      
      for (let minterm of pi) {
         const binStr = toBin(minterm, vars);
         const bit = binStr[i];
         if (bitVal === null) bitVal = bit;
         else if (bitVal !== bit) {
            isConstant = false;
            break;
         }
      }
      
      if (isConstant) {
         term += varNames[i] + (bitVal === '0' ? "'" : "");
      }
   }
   return term;
};

const generateProblem = (vars, difficulty) => {
  const totalCells = Math.pow(2, vars);
  const minterms = [];
  const dontcares = [];
  
  // Determine number of minterms based on difficulty
  let targetMinterms = Math.floor(totalCells / 2);
  if (difficulty === 'Easy') targetMinterms = Math.floor(totalCells / 4) + 1;
  if (difficulty === 'Hard') targetMinterms = Math.floor((totalCells * 3) / 4);
  
  const available = Array.from({length: totalCells}, (_, i) => i);
  
  // Shuffle and pick
  available.sort(() => Math.random() - 0.5);
  for (let i = 0; i < targetMinterms; i++) {
    minterms.push(available[i]);
  }
  
  // Add don't cares for medium/hard
  if (difficulty !== 'Easy') {
    const dcCount = difficulty === 'Hard' ? 2 : 1;
    for (let i = targetMinterms; i < targetMinterms + dcCount; i++) {
      if (available[i] !== undefined) dontcares.push(available[i]);
    }
  }
  
  minterms.sort((a, b) => a - b);
  dontcares.sort((a, b) => a - b);
  
  return { vars, minterms, dontcares };
};

export default function KMapMaster() {
  const [view, setView] = useState('home'); // home, practice, summary
  
  return (
    <div className="min-h-screen font-sans transition-colors duration-300 bg-gray-50 text-gray-900">
      {/* Header */}
      <header className="sticky top-0 z-50 backdrop-blur-md border-b border-gray-200 bg-white/80">
        <div className="max-w-6xl mx-auto px-4 h-16 flex items-center justify-between">
          <div className="flex items-center space-x-2 cursor-pointer" onClick={() => setView('home')}>
  <img
    src={logo}
    alt="KMap Master Logo"
    className="w-10 h-10 object-contain"
  />
  <span className="text-xl font-bold bg-clip-text text-transparent bg-gradient-to-r from-blue-600 to-blue-400">
    KMap Master
  </span>
</div>
          
          <nav className="hidden md:flex space-x-6">
            <button onClick={() => setView('home')} className="font-medium text-gray-600 hover:text-blue-600 transition">Home</button>
            <button onClick={() => setView('practice')} className="font-medium text-gray-600 hover:text-blue-600 transition">Practice</button>
            <button
    onClick={() => setView("rules")}
    className="font-medium text-gray-600 hover:text-blue-600 transition"
>
    Learn Rules
</button>
            <a
  href="https://www.youtube.com/playlist?list=PLG7FpyEhYMl8"
  target="_blank"
  rel="noopener noreferrer"
  className="flex items-center gap-2 font-medium text-gray-600 hover:text-red-600 transition"
>
  <FaYoutube className="text-red-600 text-lg" />
  <span>Learn</span>
</a>
          </nav>
        </div>
      </header>

      {/* Main Content Area */}
      <main className="max-w-6xl mx-auto px-4 py-8">
        <AnimatePresence mode="wait">
          {view === "home" && (
    <HomeView
        key="home"
        onStart={() => setView("practice")}
        onLearn={() => setView("rules")}
    />
)}

{view === "practice" && (
    <PracticeTutor key="practice" />
)}

{view === "rules" && (
    <RulesView
        key="rules"
        onHome={() => setView("home")}
        onPractice={() => setView("practice")}
    />
)}
        </AnimatePresence>
      </main>
    </div>
  );
}

function HomeView({ onStart, onLearn }) {
  return (
    <motion.div 
      initial={{ opacity: 0, y: 20 }}
      animate={{ opacity: 1, y: 0 }}
      exit={{ opacity: 0, y: -20 }}
      className="flex flex-col items-center mt-10 md:mt-20 text-center"
    >
      <div className="inline-flex items-center space-x-2 px-3 py-1 rounded-full bg-blue-100 text-blue-600 text-sm font-semibold mb-6">
        <span>✨ New Interactive Tutor Mode</span>
      </div>
      
      <h1 className="text-4xl md:text-6xl font-extrabold mb-6 tracking-tight text-gray-900">
        Master Karnaugh Maps <br/>
        <span className="text-transparent bg-clip-text bg-gradient-to-r from-blue-600 to-indigo-500">
          The Interactive Way
        </span>
      </h1>
      
      <p className="text-lg md:text-xl max-w-2xl text-gray-600 mb-10">
        Stop using simple calculators. KMap Master is a step-by-step digital tutor that helps you fill maps, form optimal groups, and derive simplified boolean expressions.
      </p>
      
      <div className="flex flex-col sm:flex-row space-y-4 sm:space-y-0 sm:space-x-4">
        <button 
          onClick={onStart}
          className="flex items-center justify-center space-x-2 bg-blue-600 hover:bg-blue-700 text-white px-8 py-4 rounded-xl text-lg font-bold shadow-lg shadow-blue-600/30 transition-all hover:scale-105"
        >
          <Play className="w-5 h-5" fill="currentColor" />
          <span>Start Practice</span>
        </button>
        <button
        onClick={onLearn}
         className="flex items-center justify-center space-x-2 bg-white border border-gray-200 text-gray-900 hover:bg-gray-50 px-8 py-4 rounded-xl text-lg font-bold shadow-sm transition-all">
          <BookOpen className="w-5 h-5" />
          <span>Learn Rules</span>
        </button>
      </div>
      
      {/* Features Grid */}
      <div className="grid grid-cols-1 md:grid-cols-3 gap-6 mt-20 w-full">
        {[
          { icon: <MousePointerClick className="w-6 h-6 text-blue-500"/>, title: 'Interactive Grid', desc: 'Click to cycle cell values and draw valid groupings.' },
          { icon: <Lightbulb className="w-6 h-6 text-yellow-500"/>, title: 'Smart Feedback', desc: 'Get detailed hints when you make a mistake.' },
          { icon: <CheckCircle className="w-6 h-6 text-green-500"/>, title: 'Step-by-Step Validation', desc: 'Verifies your grid, your groups, and your equation.' }
        ].map((feat, i) => (
          <div key={i} className="p-6 rounded-2xl bg-white border border-gray-100 shadow-xl shadow-gray-200/20 text-left">
            <div className="w-12 h-12 rounded-full bg-gray-50 flex items-center justify-center mb-4">
              {feat.icon}
            </div>
            <h3 className="text-xl font-bold mb-2 text-gray-900">{feat.title}</h3>
            <p className="text-gray-600">{feat.desc}</p>
          </div>
        ))}
      </div>
            {/* Footer */}
      <footer className="mt-20 w-full border-t border-gray-200 pt-8 text-center">
        <p className="text-sm text-gray-600">
          Made with <span className="text-red-500">❤️</span> by{" "}
          <span className="font-semibold text-gray-900">Rohit S Kumar</span>
        </p>

        <p className="mt-1 text-sm text-gray-500">
          Electronics & Communication Engineering
        </p>

        <p className="text-sm text-gray-500">
          College of Engineering Chengannur
        </p>

        <div className="mt-4 flex flex-col sm:flex-row items-center justify-center gap-3 text-sm">
          <a
            href="mailto:rohitskumar.rsk@gmail.com"
            className="text-blue-600 hover:underline"
          >
            📧 rohitskumar.rsk@gmail.com
          </a>

          <a
            href="https://www.linkedin.com/in/rohitskumar-rsk"
            target="_blank"
            rel="noopener noreferrer"
            className="text-blue-600 hover:underline"
          >
            💼 LinkedIn
          </a>
        </div>

        <p className="mt-5 text-sm text-gray-500 italic">
          Spotted a mistake? I'd appreciate your feedback.
        </p>
      </footer>
    </motion.div>
  );
}

function PracticeTutor() {
  const [config, setConfig] = useState({ vars: 4, difficulty: 'Medium' });
  const [problem, setProblem] = useState(null);
  
  // Steps: 'setup' -> 'fill' -> 'group' -> 'solve' -> 'result'
  const [step, setStep] = useState('setup'); 
  
  // User Data State
  const [userGrid, setUserGrid] = useState([]);
  const [userGroups, setUserGroups] = useState([]);
  const [currentSelection, setCurrentSelection] = useState(new Set());
  const [userExpr, setUserExpr] = useState('');
  
  // Feedback State
  const [feedback, setFeedback] = useState({ type: '', msg: '' });

  const startProblem = () => {
    const p = generateProblem(config.vars, config.difficulty);
    setProblem(p);
    setUserGrid(Array(Math.pow(2, config.vars)).fill(null));
    setUserGroups([]);
    setCurrentSelection(new Set());
    setUserExpr('');
    setFeedback({ type: 'info', msg: "Step 1: Fill the K-Map based on the minterms provided." });
    setStep('fill');
  };

  const checkGrid = () => {
    const totalCells = Math.pow(2, problem.vars);
    let allCorrect = true;
    let errorMsg = '';

    for (let i = 0; i < totalCells; i++) {
      const isMinterm = problem.minterms.includes(i);
      const isDontCare = problem.dontcares.includes(i);
      const userVal = userGrid[i];
      
      let expected = 0;
      if (isMinterm) expected = 1;
      if (isDontCare) expected = 'X';

      if (userVal !== expected) {
        allCorrect = false;
        if (userVal === null) errorMsg = "Some cells are empty. Fill all cells with 0, 1, or X.";
        else if (isMinterm) errorMsg = `Cell ${i} should be 1 (it's a minterm).`;
        else if (isDontCare) errorMsg = `Cell ${i} should be X (Don't care).`;
        else errorMsg = `Cell ${i} should be 0.`;
        break;
      }
    }

    if (allCorrect) {
      setFeedback({ type: 'success', msg: "Perfect! Now, group the 1s (and useful Xs) using powers of 2." });
      setStep('group');
    } else {
      setFeedback({ type: 'error', msg: errorMsg });
    }
  };

  const handleGroupSelection = () => {
    if (currentSelection.size === 0) return;
    const selectedArray = Array.from(currentSelection).sort((a, b) => a - b);
    
    // 1. Validate Shape Geometry
    const allBoxes = getAllValidBoxes(problem.vars);
    const isGeomValid = allBoxes.some(box => box.length === selectedArray.length && box.every((v, i) => v === selectedArray[i]));
    
    if (!isGeomValid) {
      setFeedback({ type: 'error', msg: "Invalid group shape or size. Groups must be contiguous rectangles (1, 2, 4, 8, 16 cells) and can wrap around edges." });
      setCurrentSelection(new Set());
      return;
    }

    // 2. Validate No 0s included
    let hasZero = selectedArray.some(cellIdx => !problem.minterms.includes(cellIdx) && !problem.dontcares.includes(cellIdx));
    if (hasZero) {
      setFeedback({ type: 'error', msg: "Groups cannot contain 0s!" });
      setCurrentSelection(new Set());
      return;
    }

    // 3. Validate Optimality (Must be a Prime Implicant)
    const PIs = getPrimeImplicants(problem.minterms, problem.dontcares, problem.vars);
    const isPI = PIs.some(pi => pi.length === selectedArray.length && pi.every((v, i) => v === selectedArray[i]));

    if (!isPI) {
       setFeedback({ type: 'error', msg: "Suboptimal group: This group can be expanded into a larger valid group using adjacent 1s or Xs. Always form the largest possible groups!" });
       setCurrentSelection(new Set());
       return;
    }

    // 4. Check for duplicates
    const isDuplicate = userGroups.some(g => 
      g.length === selectedArray.length && 
      g.every((val, index) => val === selectedArray[index])
    );
    if (isDuplicate) {
      setFeedback({ type: 'error', msg: "This exact group already exists." });
      setCurrentSelection(new Set());
      return;
    }

    setUserGroups([...userGroups, selectedArray]);
    setCurrentSelection(new Set());
    setFeedback({ type: 'info', msg: "Group added. Make sure all 1s are covered optimally with the fewest number of groups." });
  };

  const checkGroups = () => {
    // 1. Check if all 1s are covered
    const covered = new Set();
    userGroups.forEach(g => g.forEach(cell => covered.add(cell)));
    
    const missing = problem.minterms.filter(m => !covered.has(m));
    if (missing.length > 0) {
      setFeedback({ type: 'error', msg: `You missed some 1s. Minterms left to cover: ${missing.join(', ')}` });
      return;
    }

    // 2. Redundancy Check (Is any group completely covered by the combination of others?)
    for (let i = 0; i < userGroups.length; i++) {
       const otherGroups = userGroups.filter((_, idx) => idx !== i);
       const otherCovered = new Set();
       otherGroups.forEach(g => g.forEach(cell => otherCovered.add(cell)));
       
       const requiredMintermsInThisGroup = userGroups[i].filter(m => problem.minterms.includes(m));
       const isRedundant = requiredMintermsInThisGroup.every(m => otherCovered.has(m));
       if (isRedundant) {
           setFeedback({type: 'error', msg: `Redundant group detected! Group ${i + 1} is unnecessary because all its required 1s are already covered by your other groups.`});
           return;
       }
    }

    // 3. Minimum Cover Validation
    const PIs = getPrimeImplicants(problem.minterms, problem.dontcares, problem.vars);
    const minCovers = getMinimumCovers(PIs, problem.minterms, problem.vars);
    
    const sortedUserGroups = userGroups.map(g => [...g].sort((a,b)=>a-b));
    const userSig = sortedUserGroups.map(pi => pi.join('-')).sort().join('|');
    
    let isOptimalCover = false;
    for (let cover of minCovers) {
       const coverSig = cover.map(pi => [...pi].sort((a,b)=>a-b).join('-')).sort().join('|');
       if (userSig === coverSig) {
         isOptimalCover = true;
         break;
       }
    }
    
    if (!isOptimalCover) {
         const minGroupCount = minCovers.length > 0 ? minCovers[0].length : 0;
         if (userGroups.length > minGroupCount) {
            setFeedback({type: 'error', msg: `You covered all 1s without redundancy, but your solution uses ${userGroups.length} groups. A more optimal solution exists using exactly ${minGroupCount} groups. (Hint: Did you miss an Essential Prime Implicant?)`});
         } else {
            setFeedback({type: 'error', msg: `Your groups cover all 1s, but they don't form the absolute most optimal solution (minimum literals). Ensure you are choosing the largest possible groups!`});
         }
         return;
    }

    setFeedback({ type: 'success', msg: "Optimal grouping! Now, translate each group into its Boolean product term and sum them up (SOP format)." });
    setStep('solve');
  };

  const checkExpression = () => {
    if (!userExpr) {
      setFeedback({ type: 'error', msg: "Please enter an expression." });
      return;
    }

    const PIs = getPrimeImplicants(problem.minterms, problem.dontcares, problem.vars);
    const minCovers = getMinimumCovers(PIs, problem.minterms, problem.vars);
    
    // Normalizes strings like (A*B') to just AB' and sorts literals alphabetically
    const normalizeTermStr = (term) => {
      if (term === '1') return '1';
      const lits = term.match(/[A-Z]'?/gi); 
      if (!lits) return '';
      return [...new Set(lits.map(l => l.toUpperCase()))].sort().join('');
    };

    const cleanUser = userExpr.toUpperCase().replace(/[\s\*\(\)]/g, '');
    const userTerms = cleanUser.split('+').filter(t => t.length > 0);
    const normUser = userTerms.map(normalizeTermStr).sort().join('+');

    let isCorrect = false;
    let expectedGroupCount = 0;

    for (let cover of minCovers) {
       const expectedTerms = cover.map(g => groupToTerm(g, problem.vars));
       const normExpected = expectedTerms.map(normalizeTermStr).sort().join('+');
       expectedGroupCount = expectedTerms.length;
       if (normUser === normExpected) {
          isCorrect = true;
          break;
       }
    }

    if (isCorrect) {
      setFeedback({ type: 'success', msg: "Brilliant! Your minimal SOP expression is perfectly correct and optimally simplified." });
      setStep('result');
    } else {
      if (userTerms.length !== expectedGroupCount) {
         setFeedback({ type: 'error', msg: `Your expression has ${userTerms.length} terms, but the optimal solution requires exactly ${expectedGroupCount} terms.`});
      } else {
         setFeedback({ type: 'error', msg: "The expression doesn't accurately match any valid minimal Boolean form for this K-Map. Check your terms!" });
      }
    }
  };

  if (step === 'setup') {
    return (
      <div className="max-w-xl mx-auto bg-white p-8 rounded-3xl shadow-xl border border-gray-100">
        <h2 className="text-3xl font-bold mb-6 flex items-center text-gray-900">
          <Settings className="w-8 h-8 mr-3 text-blue-500"/>
          Practice Setup
        </h2>
        
        <div className="space-y-6">
          <div>
            <label className="block text-sm font-semibold mb-2 text-gray-900">Number of Variables</label>
            <div className="flex space-x-3">
              {[2, 3, 4].map(v => (
                <button
                  key={v}
                  onClick={() => setConfig({...config, vars: v})}
                  className={`flex-1 py-3 rounded-xl font-bold transition-all ${
                    config.vars === v 
                      ? 'bg-blue-600 text-white shadow-md' 
                      : 'bg-gray-100 text-gray-600 hover:bg-gray-200'
                  }`}
                >
                  {v} Variables
                </button>
              ))}
            </div>
          </div>

          <div>
            <label className="block text-sm font-semibold mb-2 text-gray-900">Difficulty</label>
            <div className="flex space-x-3">
              {['Easy', 'Medium', 'Hard'].map(d => (
                <button
                  key={d}
                  onClick={() => setConfig({...config, difficulty: d})}
                  className={`flex-1 py-3 rounded-xl font-bold transition-all ${
                    config.difficulty === d 
                      ? 'bg-blue-600 text-white shadow-md' 
                      : 'bg-gray-100 text-gray-600 hover:bg-gray-200'
                  }`}
                >
                  {d}
                </button>
              ))}
            </div>
            <p className="text-xs text-gray-500 mt-2">
              Harder difficulties include Don't Care (X) conditions.
            </p>
          </div>

          <button 
            onClick={startProblem}
            className="w-full mt-8 bg-gradient-to-r from-blue-600 to-indigo-600 hover:from-blue-700 hover:to-indigo-700 text-white py-4 rounded-xl font-bold text-lg shadow-lg flex justify-center items-center"
          >
            Generate Problem <ArrowRight className="w-5 h-5 ml-2" />
          </button>
        </div>
      </div>
    );
  }

  return (
    <div className="grid grid-cols-1 lg:grid-cols-3 gap-8">
      {/* Left Column: Problem & K-Map */}
      <div className="lg:col-span-2 space-y-6">
        
        {/* Problem Header */}
        <div className="bg-white p-6 rounded-2xl shadow-sm border border-gray-100">
          <div className="flex justify-between items-start mb-4">
            <h3 className="text-xl font-bold text-gray-900">Simplify the Expression</h3>
            <span className="px-3 py-1 bg-blue-100 text-blue-700 rounded-full text-sm font-semibold">
              {config.vars} Variables
            </span>
          </div>
          <div className="text-2xl font-mono p-4 bg-gray-50 text-gray-900 rounded-xl overflow-x-auto">
            F({LAYOUTS[problem.vars].rowVars.join(',')},{LAYOUTS[problem.vars].colVars.join(',')}) = 
            Σm({problem.minterms.join(', ')})
            {problem.dontcares.length > 0 && ` + d(${problem.dontcares.join(', ')})`}
          </div>
        </div>

        {/* K-Map Interactive Grid */}
        <div className="bg-white p-6 rounded-2xl shadow-sm border border-gray-100 flex justify-center overflow-x-auto">
          <KMapGrid 
            vars={problem.vars} 
            userGrid={userGrid} 
            setUserGrid={setUserGrid}
            step={step}
            userGroups={userGroups}
            currentSelection={currentSelection}
            setCurrentSelection={setCurrentSelection}
          />
        </div>
      </div>

      {/* Right Column: Tutor / Controls */}
      <div className="space-y-6">
        
        {/* Tutor Message Box */}
        <div className={`p-6 rounded-2xl shadow-sm border transition-colors ${
          feedback.type === 'error' ? 'bg-red-50 border-red-200' :
          feedback.type === 'success' ? 'bg-green-50 border-green-200' :
          'bg-blue-50 border-blue-200'
        }`}>
          <div className="flex items-start space-x-3">
            {feedback.type === 'error' && <XCircle className="w-6 h-6 text-red-500 mt-1 flex-shrink-0" />}
            {feedback.type === 'success' && <CheckCircle className="w-6 h-6 text-green-500 mt-1 flex-shrink-0" />}
            {feedback.type === 'info' && <Lightbulb className="w-6 h-6 text-blue-500 mt-1 flex-shrink-0" />}
            
            <div>
              <h4 className={`font-bold text-lg mb-1 ${
                feedback.type === 'error' ? 'text-red-700' :
                feedback.type === 'success' ? 'text-green-700' :
                'text-blue-700'
              }`}>
                Tutor Feedback
              </h4>
              <p className="text-gray-700 font-medium">
                {feedback.msg}
              </p>
            </div>
          </div>
        </div>

        {/* Step-Specific Controls */}
        <div className="bg-white p-6 rounded-2xl shadow-sm border border-gray-100">
          
          {/* STEP 1: FILL */}
          {step === 'fill' && (
            <div className="space-y-4">
              <h4 className="font-bold border-b border-gray-200 pb-2 mb-4 text-gray-900">Step 1: Fill Grid</h4>
              <p className="text-sm text-gray-500 mb-4">
                Click cells in the K-Map to cycle through 0, 1, and X.
              </p>
              <div className="flex space-x-2">
                <button onClick={() => setUserGrid(Array(Math.pow(2, config.vars)).fill(0))} className="flex-1 py-2 bg-gray-100 text-gray-900 rounded-lg text-sm font-semibold hover:bg-gray-200 transition-colors">Fill All 0</button>
              </div>
              <button 
                onClick={checkGrid}
                className="w-full py-3 bg-blue-600 hover:bg-blue-700 text-white rounded-xl font-bold shadow-md transition-colors"
              >
                Check K-Map
              </button>
            </div>
          )}

          {/* STEP 2: GROUP */}
          {step === 'group' && (
            <div className="space-y-4">
              <h4 className="font-bold border-b border-gray-200 pb-2 mb-4 text-gray-900">Step 2: Group 1s</h4>
              <p className="text-sm text-gray-500 mb-4">
                Click cells to select them, then click "Add Group".
              </p>
              
              {userGroups.length > 0 && (
                <div className="mb-4">
                  <h5 className="text-xs font-bold uppercase text-gray-400 mb-2">Your Groups:</h5>
                  <div className="space-y-2">
                    {userGroups.map((g, idx) => (
                      <div key={idx} className="flex justify-between items-center bg-gray-50 text-gray-900 p-2 rounded-lg text-sm border border-transparent">
                        <span>Group {idx + 1} ({g.length} cells)</span>
                        <button 
                          onClick={() => setUserGroups(userGroups.filter((_, i) => i !== idx))}
                          className="text-red-500 hover:text-red-700 transition-colors"
                        >
                          <Trash2 className="w-4 h-4" />
                        </button>
                      </div>
                    ))}
                  </div>
                </div>
              )}

              <div className="flex space-x-2">
                <button 
                  onClick={handleGroupSelection}
                  disabled={currentSelection.size === 0}
                  className="flex-1 py-3 bg-indigo-600 disabled:bg-gray-300 disabled:text-gray-500 hover:bg-indigo-700 text-white rounded-xl font-bold shadow-md transition-colors flex justify-center items-center"
                >
                  <Plus className="w-4 h-4 mr-1" /> Add Group
                </button>
                <button 
                  onClick={checkGroups}
                  className="flex-1 py-3 bg-blue-600 hover:bg-blue-700 text-white rounded-xl font-bold shadow-md transition-colors"
                >
                  Verify Groups
                </button>
              </div>
            </div>
          )}

          {/* STEP 3: SOLVE */}
          {step === 'solve' && (
            <div className="space-y-4">
              <h4 className="font-bold border-b border-gray-200 pb-2 mb-4 text-gray-900">Step 3: Final Expression</h4>
              <p className="text-sm text-gray-500 mb-4">
                Write the simplified Sum of Products (SOP) expression. Use <code>'</code> for NOT (e.g., A'B + C).
              </p>
              <input 
                type="text" 
                value={userExpr}
                onChange={(e) => setUserExpr(e.target.value)}
                placeholder="e.g. A'B + C'D"
                className="w-full px-4 py-3 bg-gray-50 border border-gray-300 text-gray-900 rounded-xl font-mono text-lg focus:ring-2 focus:ring-blue-500 outline-none uppercase placeholder-gray-400 transition-colors"
              />
              <button 
                onClick={checkExpression}
                className="w-full py-3 bg-blue-600 hover:bg-blue-700 text-white rounded-xl font-bold shadow-md transition-colors"
              >
                Check Expression
              </button>
            </div>
          )}

          {/* RESULT */}
          {step === 'result' && (
            <div className="space-y-4 text-center py-4">
              <div className="inline-flex justify-center items-center w-16 h-16 rounded-full bg-green-100 mb-2">
                <Check className="w-8 h-8 text-green-600" />
              </div>
              <h3 className="text-2xl font-bold text-green-600">Excellent Work!</h3>
              <p className="text-gray-600">You successfully simplified the K-Map.</p>
              <div className="font-mono text-xl bg-gray-100 text-gray-900 p-4 rounded-xl mt-4 border border-transparent">
                F = {userExpr.toUpperCase()}
              </div>
              <button 
                onClick={() => setStep('setup')}
                className="w-full mt-6 py-3 bg-blue-600 hover:bg-blue-700 text-white rounded-xl font-bold shadow-md transition-colors flex justify-center items-center"
              >
                <RotateCcw className="w-5 h-5 mr-2" /> Next Problem
              </button>
            </div>
          )}

        </div>
      </div>
    </div>
  );
}

function KMapGrid({ vars, userGrid, setUserGrid, step, userGroups, currentSelection, setCurrentSelection }) {
  const layout = LAYOUTS[vars];
  const gRows = vars === 2 ? GRAY_2 : vars >= 3 ? GRAY_2 : GRAY_4; 
  // Adjust grays for 3 vars (rows: 2, cols: 4) vs 4 vars (rows: 4, cols: 4)
  const actRows = vars === 4 ? GRAY_4 : GRAY_2;
  const actCols = vars >= 3 ? GRAY_4 : GRAY_2;
  
  // Group Colors
  const colors = [
    'rgba(239, 68, 68, 0.4)', // red
    'rgba(59, 130, 246, 0.4)', // blue
    'rgba(16, 185, 129, 0.4)', // green
    'rgba(245, 158, 11, 0.4)', // yellow
    'rgba(139, 92, 246, 0.4)'  // purple
  ];

  const handleCellClick = (idx) => {
    if (step === 'fill') {
      const newGrid = [...userGrid];
      const cur = newGrid[idx];
      newGrid[idx] = cur === null ? 0 : cur === 0 ? 1 : cur === 1 ? 'X' : 0;
      setUserGrid(newGrid);
    } else if (step === 'group') {
      const newSel = new Set(currentSelection);
      if (newSel.has(idx)) newSel.delete(idx);
      else newSel.add(idx);
      setCurrentSelection(newSel);
    }
  };

  // Helper to get actual minterm index based on visual row/col
  const getIndex = (rIdx, cIdx) => {
    return visualToMinterm(rIdx, cIdx, vars);
  };

  return (
    <div className="relative inline-block mt-8 ml-8">
      {/* Top Left Label */}
      <div className="absolute -top-8 -left-10 text-sm font-bold text-gray-500">
        {layout.rowVars.join('')} \ {layout.colVars.join('')}
      </div>

      {/* Column Headers (Gray Code) */}
      <div className="flex ml-8 mb-2">
        {actCols.map(cVal => (
          <div key={`col-${cVal}`} className="w-16 text-center font-mono font-bold text-gray-500">
            {toBin(cVal, layout.colVars.length)}
          </div>
        ))}
      </div>

      <div className="flex">
        {/* Row Headers (Gray Code) */}
        <div className="flex flex-col mr-2">
          {actRows.map(rVal => (
            <div key={`row-${rVal}`} className="h-16 flex items-center justify-end font-mono font-bold text-gray-500">
              {toBin(rVal, layout.rowVars.length)}
            </div>
          ))}
        </div>

        {/* The Grid itself */}
        <div 
          className="grid border-2 border-gray-400 bg-gray-200 gap-px"
          style={{ gridTemplateColumns: `repeat(${layout.cols}, minmax(0, 1fr))` }}
        >
          {actRows.map((rVal, rIdx) => (
            actCols.map((cVal, cIdx) => {
              const idx = getIndex(rIdx, cIdx);
              const val = userGrid[idx];
              
              // Determine if cell is in current selection
              const isSelected = currentSelection?.has(idx);
              
              // Render multiple group overlays if needed
              const cellGroups = userGroups.map((g, i) => g.includes(idx) ? colors[i % colors.length] : null).filter(Boolean);

              return (
                <div 
                  key={idx}
                  onClick={() => handleCellClick(idx)}
                  className={`relative w-16 h-16 flex items-center justify-center text-2xl font-bold bg-white cursor-pointer select-none transition-all
                    ${step === 'fill' ? 'hover:bg-gray-50' : ''}
                    ${isSelected ? 'ring-4 ring-inset ring-indigo-500 z-10' : ''}
                  `}
                >
                  {/* Values */}
                  <motion.span
                    key={val}
                    initial={{ scale: 0.5, opacity: 0 }}
                    animate={{ scale: 1, opacity: 1 }}
                    className={val === 1 ? 'text-blue-600' : val === 'X' ? 'text-red-500' : 'text-gray-300'}
                  >
                    {val !== null ? val : ''}
                  </motion.span>
                  
                  {/* Group Overlays */}
                  {cellGroups.map((color, i) => (
                    <div 
                      key={i}
                      className="absolute inset-1 rounded pointer-events-none"
                      style={{ 
                        backgroundColor: color,
                        border: `2px solid ${color.replace('0.4', '1')}`,
                        transform: `scale(${1 - (i * 0.1)})` // Nest them slightly if multiple
                      }}
                    />
                  ))}
                  
                  {/* Small index hint in corner */}
                  <span className="absolute bottom-1 right-1 text-[10px] text-gray-300 font-mono">
                    {idx}
                  </span>
                </div>
              );
            })
          ))}
        </div>
      </div>
    </div>
  );
}
// -------------------------------------------------------------
// NEW FEATURE: LEARN RULES VIEW
// -------------------------------------------------------------

function Callout({ type, title, text }) {
  const styles = {
    info: { bg: 'bg-blue-50', border: 'border-blue-200', text: 'text-blue-800', icon: <Info className="w-5 h-5 text-blue-500 mt-0.5" /> },
    tip: { bg: 'bg-green-50', border: 'border-green-200', text: 'text-green-800', icon: <Lightbulb className="w-5 h-5 text-green-500 mt-0.5" /> },
    note: { bg: 'bg-yellow-50', border: 'border-yellow-200', text: 'text-yellow-800', icon: <AlertTriangle className="w-5 h-5 text-yellow-500 mt-0.5" /> },
    error: { bg: 'bg-red-50', border: 'border-red-200', text: 'text-red-800', icon: <XCircle className="w-5 h-5 text-red-500 mt-0.5" /> },
  }[type];

  return (
    <div className={`mt-4 p-4 rounded-xl border flex items-start space-x-3 ${styles.bg} ${styles.border}`}>
      <div className="flex-shrink-0">{styles.icon}</div>
      <div>
        {title && <h5 className={`font-bold mb-1 ${styles.text}`}>{title}</h5>}
        <p className={`text-sm ${styles.text}`}>{text}</p>
      </div>
    </div>
  );
}

function MiniGrid({ size = 4, children }) {
  const cols = size === 4 ? 'grid-cols-4' : 'grid-cols-2';
  return (
    <div className={`grid ${cols} gap-[1px] bg-gray-300 border border-gray-300 p-[1px] rounded-lg shadow-sm w-full max-w-[200px] mx-auto mt-6 mb-4`}>
      {children}
    </div>
  );
}

function MiniCell({ val, overlays = [] }) {
  return (
    <div className="bg-white h-10 w-full relative flex items-center justify-center font-bold text-gray-800">
      <span className={val === 'X' ? 'text-red-500' : val === '1' ? 'text-blue-600' : 'text-gray-300'}>{val || ''}</span>
      {overlays.map((overlay, i) => (
        <div key={i} className={`absolute pointer-events-none ${overlay}`} />
      ))}
    </div>
  );
}

function RulesView({ onHome, onPractice }) {
  const rules = [
    {
      title: "What is a Karnaugh Map?",
      content: "A K-Map is a visual method used to simplify Boolean algebra expressions without using complex theorems. It acts as a 2D grid representation of a truth table, mapping inputs to outputs.",
      callout: { type: 'info', title: 'Why use it?', text: "K-Maps make recognizing patterns and grouping 1s easy and intuitive. Adjacent cells physically differ by only one variable, making simplification visual rather than algebraic." }
    },
    {
      title: "Gray Code Ordering",
      content: "Rows and columns use Gray Code sequence (00, 01, 11, 10) instead of standard binary. This is the secret ingredient of K-Maps!",
      visual: (
        <div className="flex justify-center space-x-2 my-6">
          {['00', '01', '11', '10'].map((code, i) => (
            <div key={code} className="flex flex-col items-center">
              <span className="bg-blue-100 text-blue-800 font-mono font-bold px-3 py-2 rounded-lg border border-blue-200">{code}</span>
              {i < 3 && <ArrowRight className="w-4 h-4 text-gray-400 mt-2" />}
            </div>
          ))}
        </div>
      ),
      callout: { type: 'error', title: 'Common Mistake', text: "Writing the sequence as 00, 01, 10, 11. Remember, 11 must come before 10 so that only one bit changes at a time!" }
    },
    {
      title: "Valid Group Sizes",
      content: "You can only group cells in powers of 2. This means groups can contain 1, 2, 4, 8, or 16 cells. No other sizes are mathematically valid for simplification.",
      visual: (
        <MiniGrid size={4}>
          {Array.from({length: 16}).map((_, i) => {
             // 4-group in top-left
             const isG4 = [0,1,4,5].includes(i);
             const g4Class = "inset-[2px] bg-green-400/30 border-2 border-green-500 rounded";
             // 2-group on right
             const isG2 = [7,11].includes(i);
             const g2Class = "inset-[2px] bg-blue-400/30 border-2 border-blue-500 rounded";
             return <MiniCell key={i} val={isG4 || isG2 ? '1' : ''} overlays={[isG4 && g4Class, isG2 && g2Class].filter(Boolean)} />
          })}
        </MiniGrid>
      ),
      callout: { type: 'note', text: "Never make a group of 3 or 6. If you see 3 adjacent 1s, you must make a group of 2 and another overlapping group of 2." }
    },
    {
      title: "Wrap Around Rule",
      content: "The K-Map is continuous! The left edge is adjacent to the right edge, and the top edge is adjacent to the bottom edge. Imagine the map folded into a donut (torus).",
      visual: (
        <MiniGrid size={4}>
          {Array.from({length: 16}).map((_, i) => {
             const isLeft = i % 4 === 0;
             const isRight = i % 4 === 3;
             let gClass = "";
             if (isLeft) gClass = "inset-y-[2px] inset-l-[2px] right-0 bg-purple-400/30 border-y-2 border-l-2 border-purple-500 rounded-l";
             if (isRight) gClass = "inset-y-[2px] inset-r-[2px] left-0 bg-purple-400/30 border-y-2 border-r-2 border-purple-500 rounded-r";
             return <MiniCell key={i} val={isLeft || isRight ? '1' : ''} overlays={[gClass].filter(Boolean)} />
          })}
        </MiniGrid>
      ),
      callout: { type: 'tip', title: 'Corner Grouping', text: "You can group all four corners together! This creates a valid 4-cell group representing the outer edges." }
    },
    {
      title: "Overlapping Groups",
      content: "Groups are allowed to overlap. In fact, they should overlap if it helps you form a larger valid group. Every '1' must be covered at least once, but can be covered multiple times.",
      visual: (
        <MiniGrid size={4}>
          {Array.from({length: 16}).map((_, i) => {
             const g1 = [5,6].includes(i);
             const g2 = [6,10].includes(i);
             let overlays = [];
             if (g1) overlays.push("inset-[3px] bg-yellow-400/30 border-2 border-yellow-500 rounded");
             if (g2) overlays.push("inset-[1px] bg-cyan-400/30 border-2 border-cyan-500 rounded");
             return <MiniCell key={i} val={g1 || g2 ? '1' : ''} overlays={overlays} />
          })}
        </MiniGrid>
      ),
      callout: { type: 'error', title: 'Redundant Groups', text: "Do not create a group whose 1s are ALL completely covered by other groups. This adds unnecessary terms to your final equation." }
    },
    {
      title: "Don't Care Conditions (X)",
      content: "Sometimes an input combination will never happen, or we don't care what the output is. These are marked as 'X'. You can treat an 'X' as a '1' if it helps make a larger group, or ignore it as a '0' if it doesn't.",
      visual: (
        <MiniGrid size={4}>
          {Array.from({length: 16}).map((_, i) => {
             const inGroup = [8,9,12,13].includes(i);
             const isX = [9,13].includes(i);
             const is1 = [8,12].includes(i);
             let overlay = inGroup ? "inset-[2px] bg-orange-400/30 border-2 border-orange-500 rounded" : "";
             return <MiniCell key={i} val={isX ? 'X' : is1 ? '1' : ''} overlays={[overlay].filter(Boolean)} />
          })}
        </MiniGrid>
      ),
      callout: { type: 'tip', text: "Never group an 'X' purely by itself or only with other 'X's. Only group them if they expand a group that contains at least one real '1'." }
    },
  ];

  return (
    <motion.div 
      initial={{ opacity: 0, y: 20 }}
      animate={{ opacity: 1, y: 0 }}
      exit={{ opacity: 0, y: -20 }}
      className="max-w-4xl mx-auto"
    >
      {/* Top Header */}
      <div className="flex items-center justify-between mb-8">
        <button 
          onClick={onHome}
          className="flex items-center text-gray-500 hover:text-blue-600 font-medium transition-colors bg-white px-4 py-2 rounded-xl border shadow-sm"
        >
          <ArrowLeft className="w-5 h-5 mr-2" /> Back to Home
        </button>
        <h1 className="text-3xl font-extrabold text-gray-900 flex items-center">
          <BookOpen className="w-8 h-8 text-blue-600 mr-3" /> Learn Rules
        </h1>
      </div>

      {/* Rules Grid */}
      <div className="grid grid-cols-1 md:grid-cols-2 gap-6 mb-8">
        {rules.map((rule, idx) => (
          <motion.div 
            key={idx}
            initial={{ opacity: 0, y: 20 }}
            animate={{ opacity: 1, y: 0 }}
            transition={{ delay: idx * 0.1 }}
            className="bg-white border border-gray-200 rounded-2xl p-6 shadow-sm hover:shadow-md transition-shadow"
          >
            <div className="flex items-center mb-4">
              <div className="w-8 h-8 rounded-full bg-blue-100 text-blue-700 font-bold flex items-center justify-center mr-3 flex-shrink-0">
                {idx + 1}
              </div>
              <h3 className="text-xl font-bold text-gray-900">{rule.title}</h3>
            </div>
            <p className="text-gray-600 leading-relaxed mb-4">
              {rule.content}
            </p>
            {rule.visual}
            {rule.callout && (
              <Callout type={rule.callout.type} title={rule.callout.title} text={rule.callout.text} />
            )}
          </motion.div>
        ))}
      </div>

      {/* Checklist Card */}
      <motion.div 
        initial={{ opacity: 0, y: 20 }}
        animate={{ opacity: 1, y: 0 }}
        transition={{ delay: 0.6 }}
        className="bg-green-50 border border-green-200 rounded-2xl p-8 mb-10 shadow-sm"
      >
        <h3 className="text-2xl font-bold text-green-800 mb-6 flex items-center">
          <CheckCircle className="w-7 h-7 mr-3 text-green-600" /> Optimal Solution Checklist
        </h3>
        <div className="grid grid-cols-1 sm:grid-cols-2 gap-4">
          {[
            "Groups contain only powers of two (1, 2, 4, 8, 16).",
            "No group contains a '0'.",
            "Every '1' is covered by at least one group.",
            "Largest possible valid groups were chosen.",
            "Overlapping was used to make groups larger.",
            "Wrap-around edges and corners were considered.",
            "No redundant groups were included.",
            "Expression simplified down to minimal literals."
          ].map((item, i) => (
            <div key={i} className="flex items-start">
              <Check className="w-5 h-5 text-green-600 mr-2 flex-shrink-0 mt-0.5" />
              <span className="text-green-900 font-medium">{item}</span>
            </div>
          ))}
        </div>
      </motion.div>

      {/* Action Footer */}
      <div className="flex justify-center mb-20">
        <button 
          onClick={onPractice}
          className="flex items-center justify-center space-x-2 bg-blue-600 hover:bg-blue-700 text-white px-10 py-5 rounded-2xl text-xl font-bold shadow-lg shadow-blue-600/30 transition-all hover:scale-105"
        >
          <Play className="w-6 h-6" fill="currentColor" />
          <span>I'm Ready, Start Practice</span>
        </button>
      </div>
    </motion.div>
  );
}