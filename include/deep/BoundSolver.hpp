#ifndef BOUNDSOLVER_HPP
#define BOUNDSOLVER_HPP

#include "Horn.hpp"
#include "DataLearner.hpp"
#include "DataLearner2.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  enum class Result_t {SAT=0, UNSAT, UNKNOWN};

  class BoundSolver
  {
  protected:

    CHCs& ruleManager;
    ExprFactory &m_efac;
    EZ3 z3;
    ZSolver<EZ3> smt;
    SMTUtils u;
    int varCnt = 0;
    ExprVector ssaSteps;
    map<Expr, ExprSet> candidates;

    HornRuleExt* tr;
    HornRuleExt* fc;
    HornRuleExt* qr;

    HornRuleExt tr_nogh;
    HornRuleExt fc_nogh;
    HornRuleExt qr_nogh;

    ExprVector decls;

    HornRuleExt tr_orig;    // for phases

    Expr invDecl;
    ExprVector invVars;
    ExprVector invVarsPr;
    int invVarsSz;
    int phaseNum = 0;
    bool hasArrays = false;

    string specName = "pre";
    string varName = "_FH_";
    string ghostVar_pref = "_gh_";
    Expr specDecl;
    ExprVector ghostVars;
    ExprVector ghostVarsPr;
    Expr decGhost0;
    Expr decGhost1;
    Expr ghost0Minus1;
    Expr ghost1Minus1;
    Expr ghostAss;
    Expr ghostValue;
    Expr previousGuard;
    Expr ghostGuardPr;
    Expr loopGuard;
    Expr loopGuardPr;
    Expr fcBodyInvVars;
    ExprSet bounds;
    ExprSet concrtBounds;
    ExprSet dataGrds;
    ExprVector phases;
    Expr mpzZero;
    Expr mpzOne;
    vector<pair<Expr, Expr>> phasePairs;
    vector<ExprVector> paths;
    ExprMap stren, grds2gh, fgrds2gh; // associate a guard (phi(vars)) with a precond of gh (f(vars))


    int strenBound;
    int debug;

    bool dg = false;
    bool data2 = false;
    bool doPhases = false;

  public:
    Expr ghostGuard;

    BoundSolver (CHCs& r, int _b, bool _dg, bool d2, bool _dp, int dbg)
      : m_efac(r.m_efac), ruleManager(r), u(m_efac), strenBound(_b),
        z3(m_efac), smt(z3), dg(_dg), data2(d2), doPhases(_dp), debug(dbg)
    {
      if(debug >= 3) outs() << "BoundSolver constructor\n";
      specDecl = mkTerm<string>(specName, m_efac);
      for (auto & a : ruleManager.chcs)
        if (a.isInductive) tr = &a;
        else if (a.isQuery) qr = &a;
        else fc = &a;
        
      tr_orig = *tr;

      fc_nogh = *fc;
      tr_nogh = *tr;
      qr_nogh = *qr;

      for (auto& dcl: ruleManager.decls) decls.push_back(dcl->left());
      invDecl = tr->srcRelation;
      invVars = tr->srcVars;
      invVarsPr = tr->dstVars;
      invVarsSz = invVars.size();
      mpzZero = mkMPZ(0, m_efac);
      mpzOne = mkMPZ(1, m_efac);
      setUpCounters();
    }

    void setUpCounters()
    {
      if (debug >= 5) outs() << "setUpCounters\n";
      for (int i = 0; i < 2; i++)
      {
        Expr new_name = mkTerm<string> (ghostVar_pref + to_string(i), m_efac);
        Expr var = bind::intConst(new_name);
        ghostVars.push_back(var);

        new_name = mkTerm<string> (ghostVar_pref + to_string(i) + "'", m_efac);
        var = bind::intConst(new_name);
        ghostVarsPr.push_back(var);
      }

      ghost0Minus1 = mk<MINUS>(ghostVars[0], mpzOne);
      ghost1Minus1 = mk<MINUS>(ghostVars[1], mpzOne);
      decGhost0 = mk<EQ>(ghostVarsPr[0], ghost0Minus1);
      decGhost1 = mk<EQ>(ghostVarsPr[1], ghost1Minus1);
      ghostAss = mk<LT>(ghostVars[0], mpzZero);
      ghostGuard = mk<EQ>(ghostVars[0], mpzZero);
      ghostGuardPr = mk<NEQ>(ghostVarsPr[0], mpzZero);
    }

    void replaceRule(HornRuleExt* hr, HornRuleExt* rule)
    {
      rule->srcRelation = hr->srcRelation;
      rule->srcVars = hr->srcVars;
      rule->dstRelation = hr->dstRelation;
      rule->dstVars = hr->dstVars;
      rule->isFact = hr->isFact;
      rule->isInductive = hr->isInductive;
      rule->isQuery = hr->isQuery;
      rule->body = hr->body;
    }

    void replaceRule(HornRuleExt* hr) {
      for (auto& rule: ruleManager.chcs) {
        if (!hr->isInductive && !hr->isQuery && !rule.isInductive && !rule.isQuery) {
          replaceRule(hr,&rule);
        }
        else if (hr->isInductive && rule.isInductive) {
          replaceRule(hr,&rule);
        }
        else if (hr->isQuery && rule.isQuery) {
          replaceRule(hr,&rule);
        }
      }
    }

    void specUpFc()
    {
      HornRuleExt* fc_new = new HornRuleExt();
      fc_new->srcRelation = specDecl;
      fc_new->srcVars.clear();
      fc_new->dstRelation = fc->dstRelation;
      fc_new->dstVars = fc->dstVars;
      fc_new->dstVars.push_back(ghostVarsPr[0]);
      fc_new->isFact = false;
      ExprVector specVars;
      ExprVector specVarsPr;
      for (int i = 0; i < invVars.size(); i++) {
        specVars.push_back(bind::intConst(mkTerm<string>(varName + to_string(i + invVars.size()), m_efac)));
        specVarsPr.push_back(bind::intConst(mkTerm<string>(varName + to_string(i + invVars.size()) + "'", m_efac)));
      }
      fc_new->srcVars = specVars;
      ExprSet fc_body;
      for (int i = 0; i < specVars.size(); i++) {
        fc_body.insert(mk<EQ>(specVars[i], invVarsPr[i]));
      }

      fc_body.insert(replaceAll(fc->body, invVarsPr, specVars));
      fc_body.insert(mk<EQ>(ghostVars[1], ghostVarsPr[0]));

      fc_new->body = conjoin(fc_body, m_efac);
      if (debug >= 5) outs() << "fc_new body: " << fc_new->body << "\n";
      fc_new->srcVars.push_back(ghostVars[1]);
      specVars = fc_new->srcVars;
      ruleManager.invVars[specDecl].clear();
      ruleManager.addDeclAndVars(specDecl,specVars);

      replaceRule(fc_new);

      fcBodyInvVars = fc_new->body;
      ExprSet temp;
      getConj(fcBodyInvVars,temp);
      bool replaced;
      for (auto e = temp.begin(); e != temp.end(); ) {
        replaced = false;
        for (auto& i: fc_new->dstVars) {
          if (contains(*e, i)) {
            e = temp.erase(e);
            replaced = true;
          }

        }
        if (!replaced) e++;
      }
      fcBodyInvVars = conjoin(temp, m_efac);

      for (auto & a : ruleManager.chcs)   // r.chcs changed by r.addRule, so pointers to its elements are broken
        if (a.isInductive) tr = &a;
        else if (!a.isInductive && !a.isQuery) fc = &a;
      tr_orig = *tr;

    }

    void setUpTr()
    {
      HornRuleExt* tr_new = new HornRuleExt();
      tr_new->srcRelation = tr->srcRelation;
      ruleManager.invVars[invDecl].clear();
      tr_new->srcVars = tr->srcVars;
      tr_new->srcVars.push_back(ghostVars[0]);
      invVars.push_back(ghostVars[0]);
      invVarsPr.push_back(ghostVarsPr[0]);
      tr_new->dstRelation = tr->dstRelation;
      tr_new->dstVars = tr->dstVars;
      tr_new->dstVars.push_back(ghostVarsPr[0]);
      tr_new->isInductive = true;
      ruleManager.addDeclAndVars(invDecl,invVars);

      ExprSet tmp;
      getConj(tr->body, tmp);
      tmp.insert(decGhost0);
      tr_new->body = conjoin(tmp, m_efac);
      replaceRule(tr_new);

      fcBodyInvVars = replaceAll(fcBodyInvVars, fc->srcVars, invVars);
      if (debug >= 5) outs() << "fcBodyInvVars: " << fcBodyInvVars << "\n";

      for (auto & a : ruleManager.chcs)    // r.chcs changed by r.addRule, so pointers to its elements are broken
        if (a.isInductive) tr = &a;
        else if (!a.isInductive && !a.isQuery) fc = &a;
      tr_orig = *tr;
    }

    void setUpQr(Expr g, Expr b)
    {
      Expr boundCond = mk<AND>(g,b);
      qr = new HornRuleExt();
      qr->srcRelation = tr->srcRelation; // Need to pick the rel from the last loop.
      qr->srcVars = tr->srcVars;
      qr->body = mk<AND>(mkNeg(loopGuard), boundCond);
      qr->dstRelation = mkTerm<string> ("fail", m_efac);
      qr->isQuery = true;
      ruleManager.hasQuery = true;

      ruleManager.addFailDecl(qr->dstRelation);
      ruleManager.addRule(qr);

      ghostValue = b->right();
      previousGuard = simplifyBool(g);
      if(debug >= 5) outs() << "GHOSTVALUE: " << ghostValue << std::endl;
      if(debug >= 5) outs() << "PREVIOUS GUARD: " << previousGuard << std::endl;
      ghostGuard = simplifyArithm(boundCond);
      ghostGuardPr = replaceAll(boundCond, invVars, invVarsPr);

      for (auto & a : ruleManager.chcs)    // r.chcs changed by r.addRule, so pointers to its elements are broken
        if (a.isInductive) tr = &a;
        else if (a.isQuery) qr = &a;
        else fc = &a;
      tr_orig = *tr;
    }

    bool setUpQueryAndSpec(Expr g, Expr b)
    {
      if (b == mk<TRUE>(m_efac)) {
        b = ghostGuard;
      }

      for (auto & a : ruleManager.chcs)
        if (a.isInductive) tr = &a;
        else if (a.isFact) fc = &a;
        else if (a.isQuery) qr = &a;
      tr_orig = *tr;

      invDecl = tr->srcRelation;
      invVars = tr->srcVars;
      invVarsPr = tr->dstVars;
      invVarsSz = invVars.size();

      if (tr == NULL)
      {
        outs() << "TR is missing\n";
        exit(0);
      }

      if (fc == NULL)
      {
        outs() << "INIT is missing\n";
        exit(0);
      }

      if(debug >= 4) 
      {
        outs() << "invVars: ";
        for (auto & v : invVars) outs() << v << " ";
        outs() << std::endl;
      }
      if(debug >= 4) outs() << "\n---> TR BODY: " << tr->body << std::endl;
      loopGuard = ruleManager.getPrecondition(tr);
      if(debug >= 4) outs() << "---> LOOP GUARD: " << loopGuard << "\n\n";
      loopGuardPr = replaceAll(loopGuard, invVars, invVarsPr);
      ruleManager.decls.clear();

      specUpFc();
      setUpTr();
      setUpQr(g, b);

      return true;
    }

    void decrementByNestedBound(Expr prevBound)
    {
      if(debug >= 5) outs() << "\n==========\n  TR body: " << tr->body << "\n\n";
      if(debug >= 5) outs() << "Previous Bound: " << prevBound << "\n";

      ExprSet conjs;
      getConj(tr->body, conjs);
      bool erased = false;
      for(auto i = conjs.begin(); i != conjs.end(); ) {
        if(contains(*i, ghostVars[0])) {
          i = conjs.erase(i);
          erased = true;
        }
        else {
          i++;
        }
      }
      if(erased) {
        conjs.insert(mk<EQ>(ghostVarsPr[0], mk<MINUS>(ghostVars[0], prevBound)));
      }
      if(debug >= 5) pprint(conjs, 2);
      tr->body = conjoin(conjs, m_efac);
      replaceRule(tr);

      for (auto & a : ruleManager.chcs)    // r.chcs changed by r.addRule, so pointers to its elements are broken
        if (a.isInductive) tr = &a;
        else if (!a.isInductive && !a.isQuery) fc = &a;
      tr_orig = *tr;
      if(debug >= 5) outs() << "\n==========\n\n";
      // exit(0);
    }

    bool checkAllOver (bool checkQuery = false, bool weak = true,
        Expr src = NULL, Expr dst = NULL)
    {
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery && !checkQuery) continue;
        if (!checkCHC(hr, candidates)) return false;
      }
      if (weak)
      {
        if (debug >= 3) outs () << "try weakening\n";

        for (auto & a : candidates)
        {
          ExprSet cannot;
          while (true)
          {
            auto it = a.second.begin();
            for (; it != a.second.end();)
            {
              Expr cand = *it;
              if (find(cannot.begin(), cannot.end(), cand) != cannot.end() ||
                  lexical_cast<string>(cand).find("gh") != std::string::npos)  // hack for now
              {
                ++it;
                continue;
              }

              if (u.implies(src, cand))
              {
                ++it;
                continue;
              }

              if (debug >= 4) outs () << "can remove: " << cand << " for " << a.first << "?\n";
              it = a.second.erase(it);
              auto res = checkAllOver(checkQuery, false, src, dst);
              if (debug >= 5)   outs () << "checkAllOver (nest):  " << res << "\n";
              if (!res)
              {
                cannot.insert(cand);
                break;
              }
            }

            auto res = (it == a.second.end());
            a.second.insert(cannot.begin(), cannot.end());
            if (res) break;
          }
        }
      }
       return true;
     }

    bool isSkippable(Expr model, ExprVector vars, map<Expr, ExprSet>& cands)
    {
      if (model == NULL) return true;

      for (auto v: vars)
      {
        if (!containsOp<ARRAY_TY>(v)) continue;
        Expr tmp = u.getModel(v);
        if (tmp != v && !isOpX<CONST_ARRAY>(tmp) && !isOpX<STORE>(tmp))
        {
          return true;
        }
      }

      for (auto & a : cands)
        for (auto & b : a.second)
          if (containsOp<FORALL>(b)) return true;

      return false;
    }

    bool checkCHC (HornRuleExt& hr, map<Expr, ExprSet>& annotations)
    {
      ExprSet checkList;
      checkList.insert(hr.body);
      Expr rel;
      if (debug >= 6) {
        if (hr.isQuery) outs() << "Query\n";
        else if (hr.isInductive) outs() << "Inductive\n";
        else outs() << "Pre\n";

      }
      {
        Expr rel = hr.srcRelation;
        ExprSet lms = annotations[rel];
        Expr overBody = replaceAll(conjoin(lms, m_efac), ruleManager.invVars[rel], hr.srcVars);
        if (debug >= 6) outs() << "overbody: " << overBody << "\n";
        getConj(overBody, checkList);
      }
      if (!hr.isQuery)
      {
        rel = hr.dstRelation;
        ExprSet negged;
        ExprSet lms = annotations[rel];
        for (auto a : lms) negged.insert(mkNeg(replaceAll(a, ruleManager.invVars[rel], hr.dstVars)));
        Expr neg = disjoin(negged, m_efac);
        if (debug >= 6) outs() << "neg: " << neg << "\n";
        checkList.insert(neg);
      }
      if (debug >= 6) { outs() << "checkList:\n"; pprint(checkList, 2); }
      auto res = bool(!u.isSat(checkList));
      return res;
    }

    bool anyProgress(vector<HornRuleExt*>& worklist)
    {
      for (auto & a : candidates)
        for (auto & hr : worklist) // if problems look here.
          if (hr->srcRelation == a.first || hr->dstRelation == a.first)
            if (!a.second.empty()) return true;
      return false;
    }

    void filterUnsat()
    {
     vector<HornRuleExt*> worklist;
     for (auto & a : candidates)
       if (!u.isSat(a.second)) {
         for (auto & hr : ruleManager.chcs)
           if (hr.dstRelation == a.first && hr.isFact)
             worklist.push_back(&hr);
       }

     multiHoudini(worklist, false);

     for (auto & a : candidates)
     {
       if (!u.isSat(a.second))
       {
         ExprVector tmp;
         ExprVector stub; 
         u.splitUnsatSets(a.second, tmp, stub);
         a.second.clear();
         a.second.insert(tmp.begin(), tmp.end());
       }
     }
    }

    bool multiHoudiniExtr(vector<HornRuleExt*>& worklist, bool recur = true)
    {
            return multiHoudini(worklist, recur);
    }

    // adapted from RndLearnerV3
    bool multiHoudini(vector<HornRuleExt*>& worklist, bool recur = true)
    {
      if (!anyProgress(worklist)) {
        if (debug >= 5) outs() << "No progress\n";
        return false;
      }
      auto candidatesTmp = candidates;
      bool res1 = true;
      for (auto & hr : worklist)
      {
        if (hr->isQuery) continue;

        if (!checkCHC(*hr, candidatesTmp))
        {
          bool res2 = true;
          Expr dstRel = hr->dstRelation;

          Expr model = u.getModel(hr->dstVars);
          if (isSkippable(model, hr->dstVars, candidatesTmp))
          {
            candidatesTmp[dstRel].clear();
            res2 = false;
          }
          else
          {
            for (auto it = candidatesTmp[dstRel].begin(); it != candidatesTmp[dstRel].end(); )
            {
              Expr repl = *it;
              repl = replaceAll(*it, ruleManager.invVars[dstRel], hr->dstVars);

              if (!u.isSat(model, repl)) { it = candidatesTmp[dstRel].erase(it); res2 = false; }
              else ++it;
            }
          }

          if (recur && !res2) res1 = false;
          if (!res1) break;
        }
      }
      candidates = candidatesTmp;
      if (!recur) return false;
      if (res1) return anyProgress(worklist);
      else return multiHoudini(worklist);
    }

    // adapted from BndExpl:: getAllTraces
    bool getAllPaths (Expr src, Expr dst, int len, ExprVector trace, vector<ExprVector>& traces)
    {
      if (len == 1)
      {
        for (auto a : phasePairs)
        {
          if (a.first == src && a.second == dst)
          {
            for (auto & b : trace)
            {
              if (a.second == b)
              {
                if (debug >= 1)
                  outs () << "cyclic paths not supported\n";
                return false;
              }
            }
            ExprVector newtrace = trace;
            newtrace.push_back(dst);
            traces.push_back(newtrace);
          }
        }
      }
      else
      {
        for (auto a : phasePairs)
        {
          if (a.first == src)
          {
            for (auto & b : trace)
            {
              if (a.second == b)
              {
                if (debug >= 1)
                  outs () << "cyclic paths not supported\n";
                return false;
              }
            }
            ExprVector newtrace = trace;
            newtrace.push_back(a.second);
            bool  res = getAllPaths(a.second, dst, len-1, newtrace, traces);
            if (!res) return false;
          }
        }
      }

      return true;
    }

    void getCombs(ExprVector& elems, int pos, vector<ExprVector>& res)
    {
      if (pos == 0)
      {
        res = {{elems[0]}, {mkNeg(elems[0])}};
      }
      else
      {
        vector<ExprVector> res2;
        for (auto comb : res)
        {
          comb.push_back(elems[pos]);
          res2.push_back(comb);
          comb.back() = mkNeg(elems[pos]);
          res2.push_back(comb);
        }
        res = res2;
      }
      if (pos + 1 < elems.size())
        getCombs(elems, pos+1, res);
    }

    void pairPhases() {
      Expr init = fcBodyInvVars;
      for (auto& p : phases) {
        if (init != p && u.isSat(init, p)) {
          phasePairs.push_back(std::make_pair(init,p));
        }
      }
      for (int i = 0; i < phases.size(); i++) {
        for (int j = 0; j < phases.size(); j++) {
          if (i == j) continue;
          if (u.isSat(tr->body,phases[i],replaceAll(phases[j],invVars,invVarsPr))) {
            phasePairs.push_back(std::make_pair(phases[i],phases[j]));
          }
        }
      }
      for (auto& p : phases) {
        if (!u.isSat(p, tr->body)) {
          phasePairs.push_back(std::make_pair(p,mk<FALSE>(m_efac)));
        }
      }
    }

    bool sortPhases() {
      ExprSet init;
      for (auto & p : phasePairs) {
        if (p.first == fcBodyInvVars) {
          init.insert(p.first);
        }
      }

      // sanity check:
      if (u.implies(fcBodyInvVars, disjoin(init, m_efac)))
      {
        if (debug >= 4) outs () << "Init cases general enough\n";
      }
      else
        assert(0 && "something is wrong in the phase construction");

      for (auto & in : init)
      {
        int len = paths.size();
        for (int i = 1; i <= phasePairs.size() ; i++) {
          bool res = getAllPaths (in, mk<FALSE>(m_efac), i, {in}, paths);
          if (!res) return false;
        }
        assert (paths.size() > len && "No paths found\n");
      }

      if (debug >= 4) {
        for (auto & p : paths)
        {
          outs () << "Found path: ";
          for (auto & pp : p)
            outs () << pp << " -> ";
          outs () << "\n";
        }
      }
      if (debug >= 3 || debug == -1)
        outs() << "# of paths " << paths.size() << "\n";

      return true;
    }

    void shrinkPrjcts(ExprVector & prjcts)
    {
      int sz = prjcts.size();
      if (debug >= 4) outs () << "shrinkPrjcts sz = " << sz << "\n";
      if (sz == 1) return;
      for (auto it = prjcts.begin(); it != prjcts.end();)
      {
        Expr cand = *it;
        if (u.implies(cand, loopGuard))
        {
          ++it;
          continue;
        }
        ExprSet vars;
        
        filter (loopGuard, bind::IsConst (), inserter (vars, vars.begin()));

        ExprVector copyNames, copyNamesPr, eq1, eq2;
        for (int i = 0; i < tr->srcVars.size(); i++)
        {
          Expr new_name = mkTerm<string> ("__eq_var_" + to_string(i), m_efac);
          Expr var = cloneVar(tr->srcVars[i], new_name);
          copyNames.push_back(var);

          new_name = mkTerm<string> ("__eq_var_" + to_string(i) + "_", m_efac);
          Expr var1 = cloneVar(tr->srcVars[i], new_name);
          copyNamesPr.push_back(var1);

          if (find(vars.begin(), vars.end(), tr->srcVars[i]) != vars.end())
          {
            eq1.push_back(mk<EQ>(tr->srcVars[i], var));
            eq2.push_back(mk<EQ>(tr->dstVars[i], var1));
          }
        }

        bool eq = true;
        for (auto c : {cand, mk<NEG>(cand)})
        {
          Expr newBody = replaceAll(replaceAll(mk<AND>(tr->body, c), tr->srcVars, copyNames),
                                              tr->dstVars, copyNamesPr);
          eq &= (true == (bool)u.isSat(newBody));
          ExprVector eqcheck = {
            tr->body,
            newBody,
            conjoin(eq1, m_efac),
            mk<NEG>(conjoin(eq2, m_efac))
          };
          eq &= (false == (bool)u.isSat(eqcheck));
        }

        if (eq)
        {
          outs () << "   >> erasing prj: " << *it << "\n";
          it = prjcts.erase(it);
          break;
        }
        else ++it;
      }
      if (prjcts.size() < sz) shrinkPrjcts(prjcts);
    }

    bool collectPhaseGuards(bool weakenPhases = false)
    {
      if(u.isFalse(qr->body)) {
        outs() << "QR is false" << std::endl;
        return false;
      }
      if(u.isFalse(mk<AND>(replaceAll(previousGuard, invVars, fc->srcVars), fc->body))) {
        outs() << "Infeasible init state" << std::endl;
        return false;
      }
      BndExpl bnd(ruleManager, (debug > 0));
      ExprSet cands;
      HornRuleExt* hr = &ruleManager.chcs[0];
      Expr rel = hr->srcRelation;
      int invNum = getVarIndex(invDecl, decls);
      ExprVector& srcVars = tr->srcVars;
      ExprVector& dstVars = tr->dstVars;
      assert(srcVars.size() == dstVars.size());
      ExprSet dstVarsSet;
      for (auto& d: dstVars) dstVarsSet.insert(d);

      ExprVector vars2keep, prjcts, prjcts1, prjcts2;
      ExprSet prjctsTmp;
      bool hasArray = false;
      for (int i = 0; i < srcVars.size(); i++) {
        if (containsOp<ARRAY_TY>(srcVars[i]))
        {
          hasArray = true;
          vars2keep.push_back(dstVars[i]);
        }
        else
        {
          vars2keep.push_back(srcVars[i]);
        }
      }

      u.flatten(tr->body, prjcts1, false, vars2keep, keepQuantifiersRepl);

      if (weakenPhases)
      {
        for (auto p1 = prjcts1.begin(); p1 != prjcts1.end(); )
        {
          bool changed = false;
          for (auto p2 = prjcts1.begin(); p2 != prjcts1.end(); p2++)
          {
            if (*p1 == *p2) { continue; }
            if (u.implies (*p1, *p2))
            {
              if (debug >= 5) outs () << "  to remove " << *p1 << "\n";
              changed = true;
            }
          }
          if (changed) { p1 = prjcts1.erase(p1); }
          else { p1++; }
        }
      }

      for (auto p : prjcts1)
      {
        if (hasArray)
        {
          p = ufo::eliminateQuantifiers(p, dstVarsSet);
          p = weakenForVars(p, dstVars);
        }
        else
        {
          p = weakenForVars(p, dstVars);
          p = simplifyArithm(normalize(p));
        }
        getConj(p, prjctsTmp);
        if (debug >= 4) outs() << "Generated MBP: " << p << "\n";
      }

      prjcts.insert(prjcts.end(), prjctsTmp.begin(), prjctsTmp.end());
      u.removeRedundantConjunctsVec(prjcts);

      for (auto it = prjcts.begin(); it != prjcts.end();)
      {
        bool toRem = false;
        for (auto it2 = prjcts.begin(); it2 != it; ++it2)
        {
          if (u.isEquiv(*it, mkNeg(*it2)))
          {
            toRem = true;
            break;
          }
        }
        if (toRem)
          it = prjcts.erase(it);
        else
          ++it;
      }
      if (debug >= 4)
      {
        outs() << "Split MBP: \n";
        pprint(prjcts, 3);
      }

      shrinkPrjcts(prjcts);

      vector<ExprVector> res;
      getCombs(prjcts, 0, res);
      for (auto & r : res)
      {
        phases.push_back(conjoin(r, m_efac));
        if (debug >= 4) {
          outs () << "  comb: ";
          pprint(r);
          outs () << "\n";
        }
      }

      pairPhases();
      if (debug >= 4) {
        outs() << "\n";
        for (auto& v: phasePairs) {
          outs() << "  : "<< v.first << " --> " << v.second << "\n";
        }
        outs() << "\n";
      }
      if (!sortPhases())
      {
        if (!weakenPhases) {
          if (debug >= 4) outs() << "Path finding failed. Trying again.\n";
          phasePairs.clear();
          paths.clear();
          phases.clear();
          collectPhaseGuards(true);
        }
        else {
          outs() << "Path finding failed.\n";
          exit(1);
        }
      }

      return true;
    }

    void parseForGuards() {
      if (debug >= 4) outs() << "Begin parsing for guards\n";
      // get a DNF form if there are disj in the result from G&S.
      ExprVector projections, prjcts, vars2keep;
      Expr pc = ghostVars[0];

      u.flatten(conjoin(candidates[specDecl], m_efac), prjcts, false, vars2keep, [](Expr a, ExprVector& b){return a;});

      for (auto& p : prjcts) {
        projections.push_back(replaceAll(p, fc->srcVars, invVars));
      }
      if (debug >= 4) {
        outs() << "\n   Projections\n=================\n";
        pprint(projections, 3);
        outs() << "=================\n";
      }
      ExprSet t,p,g;
      for (auto e = projections.begin(); e != projections.end() ; e++) {
        t.clear(); p.clear(); g.clear();
        getConj(*e, t);

        ExprSet temp;
        for (auto& a: t) {
          temp.insert(normalize(a));
        }
        t.clear();
        t.swap(temp);
        int c = 0;
        ExprSet toBeRenamed;
        for (auto& ee: t) {
          if (contains(ee, ghostVars[0]) || contains(ee, ghostVars[1])) {
            c++;
            Expr r = replaceAll(ee, fc->srcVars, invVars);

            r = normalize(r, pc);
            if (containsOp<EQ>(r) && r->left() == pc) g.insert(r);
            else toBeRenamed.insert(r);
          }
          else {
            Expr r = replaceAll(ee, fc->srcVars,invVars);
            p.insert(normalize(r));
          }
        }

        Expr join = *g.begin();
        auto i = g.begin(), end = g.end();
        i++;
        for (auto & a : toBeRenamed)
          p.insert(replaceAll(a, pc, join->right()));
        for (; i!=end; i++) {
          join = mk<EQ>(join->right(), (*i)->right());
          join = normalize(join);
          p.insert(join);
        }
        for (auto& d: g) {
          if (isOpX<MPZ>(d->right())) {
            join = d;
            break;
          }
        }

        auto grd = conjoin(p, m_efac);
        if (grds2gh[grd] != NULL && join->right() != grds2gh[grd])
        {
          if(debug >= 4) {
            outs () << "grds2gh for " << grd << ":\n   " << grds2gh[grd] << "\n";
            outs () << "   want to assign: " << join->right() << "\n";
          }
          continue;
        }
        {
          if(debug >= 4) outs () << "  ASSIGNING grds2gh for " << grd << ":\n   " << join->right() << "\n";
          grds2gh[grd] = join->right();  // GF: DS
        }
      }
      if (debug >= 4) { outs() << "End parsing for guards\n"; }
    }

    void genCands(ExprSet & tmp, Expr pc)
    {
      Expr v = mkConst(mkTerm<string>("tmp_", m_efac), mk<INT_TY>(m_efac));
      ExprSet newCands;
      for (auto it = tmp.begin(); it != tmp.end(); ++it)
      {
        auto a = *it;
        if (contains(a, pc)) continue;
        if (!isOp<ComparissonOp>(a)) continue;
        a = normalize(a);

        for (auto it2 = std::next(it); it2 != tmp.end(); ++it2)
        {
          auto b = *it2;
          if (a == b) continue;
          if (!isOp<ComparissonOp>(b)) continue;
          b = normalize(b);

          Expr n = mk<AND>(reBuildCmp(a, mk<MINUS>(a->left(), a->right()), v),
                           reBuildCmp(b, mk<MINUS>(b->left(), b->right()), v));
          newCands.insert(eliminateQuantifier(n, v));
        }
      }
      tmp = newCands;
    }

    void bubbleSort(ExprVector& v) {
      for (int i = 0; i < v.size(); i++) {
        for (int j = 0; j < v.size()-1; j++) {
          if (v[j]->left()->arity() > v[j+1]->left()->arity()) {
            Expr e = v[j];
            v[j] = v[j+1];
            v[j+1] = e;
          }
        }
      }
    }

    void sortBounds(ExprVector& bounds) {
      ExprVector holdMPZ, holdOther;

      for (int i = 0; i < bounds.size(); i++) {
        Expr e = normalize(bounds[i]);
        if (e->arity() > 0 && isOpX<MPZ>(e->right()) && e->right() != mpzZero) {
          holdMPZ.push_back(e);
        }
        else {
          holdOther.push_back(e);
        }
      }
      bubbleSort(holdOther);
      bubbleSort(holdMPZ);
      bounds.clear();
      for (auto& v : holdOther) bounds.push_back(normalize(v, ghostVars[0]));
      for (auto& v : holdMPZ) bounds.push_back(normalize(v, ghostVars[0]));
    }

    void filterNonGhExp(ExprSet& candSet)
    {
      for (auto i = candSet.begin(); i != candSet.end(); ) {
        if (!contains(*i, ghostVars[0])) {
          if (dg) dataGrds.insert(*i);
          i = candSet.erase(i);
        }
        else i++;
      }
      ExprSet tmp;
      for (auto i = candSet.begin(); i != candSet.end();)
      {
        Expr e = normalize(*i, ghostVars[0]);
        if(isOpX<MULT>(e->left()) && false) i = candSet.erase(i);
        else
        {
          tmp.insert(e);
          i++;
        }
      }
      candSet = tmp;
    }

    boost::tribool dataForBoundPhase(Expr src, Expr dst,
                                     map<Expr, ExprSet>& candMap, Expr block) {
      DataLearner2 dl2(ruleManager, z3, debug);
      Expr invs = mk<TRUE>(m_efac);
      boost::tribool res = true;
      Expr pc = ghostVars[0];
      assert (grds2gh[dst] != NULL);

      qr->body = mk<AND>(mk<NEG>(src),
                         mk<NEG>(mk<AND>(dst, stren[dst],
                                 mk<EQ>(pc, grds2gh[dst])))); // hack for now
      tr->body = u.removeITE(mk<AND>(src, tr_orig.body));

      if (debug > 5) {
        outs () << "  using " << grds2gh[dst] << "\n    as bound for " << dst << "\n";
        outs() << "PC = GRDS2GH[DST]: " << mk<EQ>(pc, grds2gh[dst]) << std::endl;
      }

      auto dst1 = mk<AND>(mk<NEG>(src), mk<AND>(previousGuard, dst, stren[dst]), mk<EQ>(pc, grds2gh[dst]));

      if(debug >= 5) {
        outs() << "BLOCK: " << block << std::endl;
        outs() << "SRC: " << src << std::endl;
        outs() << "SRC2: " << src << std::endl;
      }

      auto src1 = u.simplifiedAnd(block, src);
      if(debug >= 5) {
        outs() << "SRC1: " << src1 << std::endl;
        outs() << "DST1: " << dst1 << std::endl;
      }
      if(u.isFalse(dst1)) {
        if(debug >= 5) {
          outs() << "dst1 is false" << std::endl;
        }
        return false;
      }

      if (isOpX<TRUE>(block)) {
        src1 = replaceAll(src1, invVars, fc->srcVars);
      }

      res = dl2.connectPhase(src1, dst1, 3, invDecl, block, invs, loopGuard);
      if (res == true) {
        dl2.getDataCands(candMap[invDecl], invDecl);  // GF
      }
      else
      {
        if(debug >= 3)
          outs () << "check sanity:\n";
        if(debug >= 4) {
          outs () << src1 << "   =>  \n";
          outs () << dst << "\n";
        }
        ExprSet cnjs, cnjsUpd;
        getConj(src1, cnjs);
        // some small mutations
        for (auto s : cnjs)
        {
          s = simplifyArithm(replaceAll(
              keepQuantifiers(mk<AND>(s, tr->body), tr->dstVars),
              tr->dstVars, tr->srcVars));

          getConj(s, cnjsUpd);
        }
        cnjs.insert(cnjsUpd.begin(), cnjsUpd.end());

        for (auto it = cnjs.begin(); it !=cnjs.end();)
          if (u.implies(mk<AND>(*it, tr->body),
                   replaceAll(*it, tr->srcVars, tr->dstVars)))
            ++it; else it = cnjs.erase(it);
      }

      if(debug >= 5) {
        for(auto& e : candMap[invDecl]) {
          outs() << "candMap: " << e << "\n";
        }
      }
      return res;
    }

    boost::tribool exploreBounds(Expr src, Expr dst,
                                 map<Expr, ExprSet>& ghCandMap, Expr block)
    {
      boost::tribool res;

      if (isOpX<FALSE>(block)) return false;
      res = dataForBoundPhase(src, dst, ghCandMap, block);
      if (res == indeterminate) return indeterminate;
      else if (res == false) return false;
      filterNonGhExp(ghCandMap[invDecl]);
      if (ghCandMap[invDecl].empty()) return indeterminate;

      ExprSet temp;
      for (auto i = ghCandMap[invDecl].begin(),
          end = ghCandMap[invDecl].end(); i != end; i++) {
        Expr e = *i;
        e = normalize(e,ghostVars[0]);
        temp.insert(e);
      }
      ghCandMap[invDecl].swap(temp);
      if (debug >= 4) {
        outs() << "  Filtered cands found: ";
        if (!ghCandMap[invDecl].empty())
          outs() << ghCandMap[invDecl].size() << "\n";
        else outs() << "  none.\n";
      }
      if(debug >= 5) {
        for(auto& e: ghCandMap[invDecl]) {
          outs() << "ghCandMap[" << invDecl << "]: " << e << "\n";
        }
      }

      return res;
    }

    Result_t elba(ExprSet& third, Expr src, Expr dst)
    {
      if (debug >= 3)
        outs() << "\n  ===================\n" <<
                    "  ||    E L B A    || \n" <<
                    "  ===================\n\n";

      filterUnsat();
      Expr pc = ghostVars[0];
      vector<HornRuleExt*> worklist;
      for (auto & hr : ruleManager.chcs)
      {
        if (containsOp<ARRAY_TY>(hr.body)) hasArrays = true;
        worklist.push_back(&hr);
      }
      if (debug > 5) outs () << "stage 0\n";
      auto candidatesTmp = candidates;
      multiHoudiniExtr(worklist);


      // stage 0:
      if (checkAllOver(true, true, src, dst)) return Result_t::UNSAT;

      if (strenBound == 0) return Result_t::UNKNOWN;

      Expr learnedLemmasInv = conjoin(candidates[invDecl], m_efac);
      candidates = candidatesTmp;
      for (auto & a : candidatesTmp[invDecl])
      {
        if (!isOp<ComparissonOp>(a)) continue;
        if (isOpX<EQ>(a)) continue;
        if (contains(a, pc)) continue;
        ExprVector vars, varsPr;
        for (int i = 0; i < tr->dstVars.size(); i++)
        {
          if (!contains(a, tr->srcVars[i])) continue;
          vars.push_back(tr->srcVars[i]);
          varsPr.push_back(tr->dstVars[i]);
        }

        auto b = replaceAll(
                  keepQuantifiers(mk<AND>(a, learnedLemmasInv, tr->body), varsPr),
                  varsPr, vars);
        getConj(mk<AND>(a, b), candidates[invDecl]);
      }

      if (debug > 5) outs () << "stage 1\n";
      candidatesTmp = candidates;
      multiHoudiniExtr(worklist);

      // stage 1:
      if (checkAllOver(true, true, src, dst)) return Result_t::UNSAT;

      if (strenBound == 1) return Result_t::UNKNOWN;


      candidates = candidatesTmp;
      for (auto & c : third)
      {
        candidates[specDecl].insert(replaceAll(c, tr->srcVars, fc->srcVars));
        candidates[invDecl].insert(c);
      }

      if (debug > 5) outs () << "stage 2\n";
      multiHoudiniExtr(worklist);

      // stage 2:
      if (checkAllOver(true, true, src, dst)) return Result_t::UNSAT;

      if (strenBound == 2) return Result_t::UNKNOWN;

      return Result_t::UNKNOWN;

      ExprSet cnjs, cnjsUpd;
      getConj(stren[dst], cnjs);
      for (auto s : cnjs)
      {
        s = simplifyArithm(u.removeITE(u.simplifiedAnd(
          mkNeg(keepQuantifiers(mkNeg(mk<IMPL>(tr->body,
                    replaceAll(s, tr->srcVars, tr->dstVars))),
                      tr->srcVars)),
          replaceAll(conjoin(candidates[specDecl], m_efac),
                      fc->srcVars, tr->srcVars))));

        getConj(s, cnjsUpd);
      }
      for (auto & c : cnjsUpd)
      {
        candidates[specDecl].insert(replaceAll(c, tr->srcVars, fc->srcVars));
        candidates[invDecl].insert(c);
      }

      if (debug > 5) outs () << "stage 3\n";
      multiHoudiniExtr(worklist);

      // stage 3:
      if (checkAllOver(true, true, src, dst)) return Result_t::UNSAT;

      return Result_t::UNKNOWN;
    }

    ExprSet exploredBounds;
    ExprSet zs;
    boost::tribool boundSolveRec(Expr src, Expr dst, Expr block, int lvl = 0) {
      map<Expr,ExprSet> bounds;
      dataGrds.clear();
      if(debug >= 5) outs() << "Begin boundSolveRec" << std::endl;
      if(debug >= 5) outs() << "LOOPGUARD: " << loopGuard << std::endl;
      if (!u.isSat(fcBodyInvVars,loopGuard)) {
        if (debug >= 4) outs() << "PROGRAM WILL NEVER ENTER LOOP\n";
        return true;
      }
      if (debug >= 4) {
        outs() << "  boundSolveRec [" << lvl << "]:\n    " << block << "\n";
      }

      if (isOpX<FALSE>(dst))
      {
        grds2gh[src] = ghostValue;

        if (debug >= 4) outs () << "  assign 0 grds2gh (0) for " << src << "\n";
        return true;
      }

      boost::tribool res = exploreBounds(src, dst, bounds, block);
      if (res == false)
      {
        if(debug >= 5) {
          outs() << "exploreBounds returned false" << std::endl;
        }
        return true;
      }
      else if (res == indeterminate) {
        outs () << "unknown\n";     
        exit(0);
        // return indeterminate;
      }

      ExprSet grds, grdsDst;
      getConj(dst, grdsDst);
      genCands(grdsDst, ghostVars[0]);
      getConj(src, grds);

      zs.clear();
      if (dg) {
        for (auto& e: dataGrds) {

          ExprSet vars;
          filter (e, bind::IsConst (), inserter (vars, vars.begin()));

          if (isOpX<EQ>(e)){

           if (!hasMPZ(e) && vars.size() > 1)
            {
              grds.insert(e);
              if (debug >= 4)
                outs() << "Adding guard from data: " << e << "\n";
            }
            else {
              if (lexical_cast<string>(e->right()) == "0" && vars.size() == 1)
                zs.insert(*vars.begin());
            }
          }
        }
      }
      if (debug >= 4)
        for (auto& e: grds) outs() << "    grd: " << e << "\n";

      if (bounds[invDecl].size() == 0) res = false;

      ExprVector boundsV, tmpBounds, tmpGuards;
      for (auto& e: bounds[invDecl])
      {
        if (!isOpX<MULT>(e->left()))
        {
          boundsV.push_back(e);
        }
        else if (tmpBounds.empty())
        {
          ExprSet vars;
          filter (e, bind::IsConst (), inserter (vars, vars.begin()));
          if (vars.size() < 3) continue; // hack, to avoid short cands

          if (isOpX<MPZ>(e->left()->left()) && e->left()->right() == ghostVars[0])
          {
            tmpBounds.push_back(mk<EQ>(ghostVars[0], mk<IDIV>(e->right(), e->left()->left())));
            tmpGuards.push_back(mk<EQ>(mk<MOD>(e->right(), e->left()->left()), mkMPZ(0, m_efac)));
            if (debug > 4) outs () << "IDIVs:\n  " << tmpBounds.back() << "\n  " << tmpGuards.back() << "\n";
          }
        }
      }

      if (strenBound == 10 && boundsV.empty() && !tmpBounds.empty())
      {
        boundsV.push_back(tmpBounds[0]);
        grds.insert(tmpGuards.begin(), tmpGuards.end());
      }

      ExprSet nb;
      for (auto & a : boundsV)
        for (auto & z : zs)
          nb.insert(mk<EQ>(a->left(), mk<PLUS>(a->right(), z)));

      boundsV.insert(boundsV.end(), nb.begin(), nb.end());
      sortBounds(boundsV);

      if (debug >= 4) {
        outs() << "\n  Bounds found this iteration\n";
        for (auto& e: boundsV) {
          outs() << "    " << e << "\n";
        }
      }

      bool rerun = false;
      for (auto b = boundsV.begin(), end = boundsV.end(); b != end && res; b++) {
        if(debug >= 4) for(auto e: exploredBounds) outs() << "exploredBounds: " << e << "\n";
        if(exploredBounds.find(*b) != exploredBounds.end()) { continue; }
        candidates.clear();
        exploredBounds.insert(*b);
        if (rerun) {
          if (debug >= 5) outs() << "RERUN\n=====\n";
          b--;
          for (auto& e: fgrds2gh) {
            candidates[invDecl].insert(e.first);
          }
        }
        else {
          for (auto& e: grds) {
            candidates[specDecl].insert(replaceAll(e, tr->srcVars, fc->srcVars));
            candidates[invDecl].insert(e);
          }
        }
        candidates[specDecl].insert(replaceAll(*b, tr->srcVars, fc->srcVars));
        candidates[invDecl].insert(*b);

        ExprSet factCands;
        getConj(keepQuantifiers(fc->body, fc->srcVars), factCands);
        for (auto & c : factCands)
        {
          candidates[specDecl].insert(c);
          candidates[invDecl].insert(replaceAll(c, fc->srcVars, tr->srcVars));
        }

        if (debug >= 4) outs() << "\n  >> Considering bound " << *b << "\n\n";

        Result_t res_t = elba(grdsDst,
          mk<AND>(src, replaceAll(src, tr->srcVars, fc->srcVars)), dst);

        if (debug >= 3) {
          outs() << "==================\n";
          printCandsEx();
          outs() << "==================\n";
        }

        if (res_t == Result_t::UNKNOWN) {
          candidates.clear();
          if (!rerun) {
            rerun = true;
          }
          else {
            rerun = false;
          }
          if (debug >= 3) outs() << "  unknown\n\n";
          if (std::next(b) == end) {
            if (phaseNum < phases.size()) {
              boundSolveRec(src, dst, mk<TRUE>(m_efac), lvl);
            }
          }
          if(debug >= 5) {
            outs() << "boundSolveRec continuing" << std::endl;
          }
          continue;
        }

        if (debug >= 4) outs() << "  >> unsat (bound is good)\n";
        rerun = false;

        parseForGuards(); // Associates guards (pre(Vars)) with Expr gh = f()
                                 // They are stored in grds2gh map.

        if (debug >= 4) {
          outs() << "  Guards/bounds:\n";
          for (auto& g: grds2gh) {
            outs() << "    (*)  " << g.first << "";
            outs() << "  ->  " << g.second << "\n";
          }
        }

        // end of parsing guards.
        ExprSet grds2;
        for (auto& g: grds2gh) {
          if (u.implies(g.first, src))
            grds2.insert(g.first);
        }
        Expr grd = disjoin(grds2,m_efac);
        if (debug >= 5) outs() << "mkNeg(grd): " << mkNeg(grd) << " AND " << src << std::endl;;
        if (u.isSat(mkNeg(grd), src)) {
          if (boundSolveRec(src, dst, mkNeg(grd), lvl + 1)) {
            exploredBounds.clear();
            return true;
          }
        }
        else
        {
          return true;
        }
      }
      if(debug >= 5) outs() << "End boundSolveRec" << std::endl;
      return false;
    }

    void boundSolve(Expr src, Expr dst)
    {
      if (debug >= 4) outs () << "  BOUNDS SOLVE: " << src << " -> " << dst << "\n";
      Expr block = mk<TRUE>(m_efac);
      if (!boundSolveRec(src, dst, block)) {
        outs() << "unknown\n";
        exit(0);
      }
      else {
        if(debug >= 4) outs() << "boundSolveRec returned true" << std::endl;
      }
    }

    ExprSet pathsSolve()
    {
      ExprSet finals;
      for (auto & p : paths)
      {
        if (debug >= 2) {
          outs () << "\n===== NEXT PATH =====\n    ";
          for (int i = 0; i < p.size(); i++) {
            if(i > 0) outs() << " -> ";
            outs() << p[i];
          }
          outs () << "\n";
        }

        Expr ant = mk<AND>(previousGuard,p[p.size()-2]);
        ant = normalize(ant);
        ant = simplifyArithm(ant);
        if(u.isFalse(ant)) continue;

        assert(p.size() > 1);
        Expr res;
        int i;
        for (i = p.size() - 2; i >= 0; i--)
        {
          if (debug >= 4) outs () << "STEP " << i << "\n";

          if (p[i] == fcBodyInvVars)
          {
            assert(i == 0);
            stren[p[i]] = NULL;
            break;
          }

          boundSolve(p[i], p[i+1]);

          res = NULL;
          ExprSet pre;
          for (auto& g: grds2gh)
          {
            if (u.implies(g.first, p[i]))
            {
              pre.insert(g.first);
              if (res == NULL) res = g.second;
              else res = mk<ITE>(g.first, g.second, res);
            }
          }
          stren[p[i]] = simplifyBool(distribDisjoin(pre, m_efac));
          if(debug >= 4) outs() << "stren[" << i << "] : " << stren[p[i]] << std::endl;
          if (i != 0) grds2gh[p[i]] = res;
        }
        ant = mk<AND>(previousGuard,stren[p[1]]);
        ant = normalize(ant);
        ant = simplifyArithm(ant);
        if(ant == mk<FALSE>(m_efac)) {
          if(stren[p[1]] == mk<FALSE>(m_efac)) { if (debug >= 3) outs() << "stren ele FALSE" << std::endl; continue; }
          finals.insert(mk<IMPL>(stren[p[1]], mk<EQ>(ghostVars[0], res)));
        }
        else {
          finals.insert(mk<IMPL>(ant, mk<EQ>(ghostVars[0], res)));
        }
        grds2gh.clear();
        stren.clear();
      }
      return finals;
    }

    void printCandsEx(bool ppr = true) {
      for (auto& a: candidates) {
        outs() << "(define-fun " << *a.first << " (";
        for (auto & b : ruleManager.invVars[a.first])
        {
          outs() << "(" << *b << " " << u.varType(b) << ")";
        }
        outs() << ") Bool\n";

        if (ppr) pprint(a.second, 3);
        else u.print(conjoin(a.second,m_efac));
        outs() << "\n\n";
      }
    }

    void printPhases() {
      outs() << "*** Phases ***\n========\n";
      for (auto& p: phases) outs() << p << "\n";
      outs() << "========\n";
    }

    void removeQuery() {
      for(auto hr = ruleManager.chcs.begin(); hr != ruleManager.chcs.end(); ) {
        if(hr->isQuery) {
          if (debug >= 5) outs() << "erasing query\n";
          hr = ruleManager.chcs.erase(hr);
        }
        else { hr++; }
      }
    }

    Expr getFcBodyInvVars() { return fcBodyInvVars; }

    
  }; // End class BoundSolver.
  // *************************

  inline void learnBounds(string smt, int inv, int stren, bool dg,
                          bool data2, bool doPhases, int debug = 0)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3, debug);
    ruleManager.parse(smt, false);
    if (debug >= 6)
    {
      ruleManager.print(false);
      outs() << ruleManager.cycles.size() << "\n";
      for (auto &cc : ruleManager.cycles)
      {
        outs() << "Cycle: " << cc.first << "  ";
        outs() << "Size: " << cc.second.size() << "\n";
        for (auto &c : cc.second)
        {
          outs() << "  ";
          for (auto e : c)
          {
            outs() << e << ", ";
          }
          outs() << "\n";
        }
      }
    }

    if (debug >= 4)
    {
      for (auto &hr : ruleManager.decls)
        outs() << hr->left() << ", ";
      outs() << "\n";
    }

    BoundSolver bs(ruleManager, inv, dg, data2, doPhases, debug);
    bs.removeQuery();
    bs.setUpQueryAndSpec(mk<TRUE>(m_efac), mk<TRUE>(m_efac));
    bs.collectPhaseGuards();
    bs.pathsSolve();

  }
} // end namespace ufo


#endif
