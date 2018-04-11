#region License
// Copyright (c) 2016 Timothy Slater
//
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use,
// copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the
// Software is furnished to do so, subject to the following
// conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
// OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
// HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
// WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.
#endregion

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using TraceWizard.Data;

namespace TraceWizard.Processors
{
    public class CobolExecutionPathProcessor : ITraceProcessor
    {
        List<ExecutionCall> allCalls;
        List<ExecutionCall> executionCalls;
        List<ExecutionCall> sqlCalls = new List<ExecutionCall>();

        Stack<ExecutionCall> callChain = new Stack<ExecutionCall>();
        List<SQLStatement> sqlStatementForCursor = new List<SQLStatement>();

        public List<SQLStatement> Statements;
        private SQLStatement currentStatement;
        string _prevLine;
        int _maxCallDepth;
        long _sqlExecCallCount;
        long _sqlExceptionCount;

        Regex contextMarker = new Regex("PSAPPSRV\\.\\d+ \\(\\d+\\)");
        Regex startMarker = new Regex(">>> start\\s+Nest=(\\d+)\\s+(.*)");
        Regex startExtMarker = new Regex(">>> start-ext\\sNest=(\\d+)\\s(.*)");
        Regex endMarker = new Regex("<<< end\\s+Nest=(\\d+)\\s+(.*?)\\s+Dur=(\\d+\\.\\d+)");
        Regex endExtMarker = new Regex("<<< end-ext\\s+Nest=(\\d+)\\s+(.*?)\\s+Dur=(\\d+\\.\\d+)");
        Regex callMarker = new Regex("(\\d+\\.\\d+)(\\s+)call\\s+(.*?)\\s+(.*)");
        Regex sqlStatement = new Regex("RC=(\\d+) Dur=(\\d+\\.\\d+) COM Stmt=(.*)");
        Regex ppcExceptionStatement = new Regex("ErrorReturn->(.*)");
        Regex parameterStatement = new Regex("\\s+[^=]+\\=\\[^=]*");

        Regex resumeMarker = new Regex(">>> resume\\s+Nest=(\\d+)\\s+(.*)");
        Regex reendMarker = new Regex(">>> reend\\s+Nest=(\\d+)\\s+(.*)");

        Regex newStatement = new Regex("^\\d+:\\d+:\\d+.\\d+\\s*(\\d+).*#(\\d+).*(COM|CEX) Stmt=(.*)");
        Regex statementName = new Regex("GETSTMT Stmt(\\(cached\\)|)=(\\w+)");

        Regex lineAndCursorMarker = new Regex("^\\d+:\\d+:\\d+.\\d+\\s*(\\d+).*#(\\d+)");
        Regex lineValid = new Regex("(CEX Stmt=)|(COM Stmt=)|(GETSTMT Stmt=)|(GETSTMT Stmt\\(cached\\)=)|(Bind position=\\d+)|(Bind-\\d+)|(Commit)|(Disconnect)");

        Regex cursorCommit = new Regex("^\\d+:\\d+:\\d+.\\d+\\s*(\\d+).*#(\\d+)\\s+RC=(\\d+)\\s+(Commit)");
        Regex cursorDisconnect = new Regex("#(\\d+)\\s+RC=\\d+\\s+Disconnect");

        Regex bindStatementType = new Regex("Bind(\\sposition=|-)(\\d+), type=(\\w+)");
        Regex bindStatementValue = new Regex("length=(\\d+), value=(.*)");
        Regex bindStatementSQLPSPDValue = new Regex("precision=(\\d+), scale=(\\d+), value=(.*)");

        Regex errorLine = new Regex("ERR rtncd=(\\d+) msg=(.*)");
        Regex errPosStatement = new Regex("EPO error pos=(\\d+)");

        Regex execStatement = new Regex("RC=(\\d+)\\s+EXE");
        Regex fetchStatement = new Regex("RC=(\\d+)\\s+Fetch");

        public void ProcessorInit(TraceData data)
        {
            executionCalls = data.ExecutionPath;
            allCalls = data.AllExecutionCalls;
            Statements = data.SQLStatements;
            sqlStatementForCursor.Add(new SQLStatement());
        }

        public void ProcessorComplete(TraceData td)
        {
            foreach (ExecutionCall call in sqlCalls)
            {
                var lineNumber = call.StartLine;

                var sqlStatement = td.SQLStatements.Where(s => s.LineNumber == lineNumber).First();

                call.SQLStatement = sqlStatement;
                sqlStatement.ParentCall = call.Parent;
                call.Duration = sqlStatement.Duration;
                if (sqlStatement.IsError)
                {
                    call.HasError = true;
                    var parent = call.Parent;
                    while (parent != null)
                    {
                        parent.HasError = true;
                        parent = parent.Parent;
                    }
                }
            }

            /* process stack traces from TraceDatta */
            foreach (StackTraceEntry traceEntry in td.StackTraces)
            {
                var x = FindCallForLineNumber(traceEntry.LineNumber);
                if (x == null)
                {
                    // sometimes they get printed right after the exit, try 1 line number above
                    x = FindCallForLineNumber(traceEntry.LineNumber - 1);
                }
                if (x != null)
                {
                    x.IsError = true;
                    x.StackTrace = traceEntry;
                    traceEntry.Parent = x;
                    var parent = x.Parent;
                    while (parent != null)
                    {
                        parent.HasError = true;
                        parent = parent.Parent;
                    }
                }
            }

            td.MaxCallDepth = _maxCallDepth;

            td.Statistics.Add(new StatisticItem() { Category = "Execution Path", Label = "Maximum Call Depth", Value = _maxCallDepth.ToString() });
            td.Statistics.Add(new StatisticItem() { Category = "Execution Path", Label = "Total Calls", Value = _sqlExecCallCount.ToString() });
            td.Statistics.Add(new StatisticItem() { Category = "Execution Path", Label = "PeopleCode Exceptions", Value = _sqlExceptionCount.ToString() });

        }

        ExecutionCall FindCallForLineNumber(long lineNumber)
        {
            ExecutionCall call = null;
            call = allCalls.Where(c => c.StartLine <= lineNumber && c.StopLine >= lineNumber).Last();

            return call;
        }

        Boolean newExecution(string currLine, string prevLine)
        {
            Match mCurr = lineAndCursorMarker.Match(currLine);
            Match mPrev = lineAndCursorMarker.Match(prevLine);
            if (mCurr.Success && mPrev.Success)
            {
                if (int.Parse(mCurr.Groups[2].Value) != int.Parse(mPrev.Groups[2].Value))
                {
                    return true;
                }
                if (mCurr.Groups[2].Value == mPrev.Groups[2].Value)
                {
                    mCurr = bindStatementType.Match(currLine);
                    mPrev = bindStatementType.Match(prevLine);
                    if (mCurr.Success && mPrev.Success)
                    {
                        if ((mCurr.Groups[2].Value == "1") || (int.Parse(mCurr.Groups[2].Value) < int.Parse(mPrev.Groups[2].Value)))
                        {
                            return true;
                        }
                    }
                }
            }

            return false;

        }

        private void addToChain(ExecutionCall call, long stopLineNumber)
        {
            allCalls.Add(call);
            //call.Duration = Double.Parse(m.Groups[1].Value);
            if (callChain.Count > 0 && callChain.Peek().indentCount == call.indentCount)
            {
                var popped = callChain.Pop();
                if (popped.StopLine == 0)
                {
                    popped.StopLine = stopLineNumber;
                }
            }

            if (callChain.Count > 0 && callChain.Peek().Type == ExecutionCallType.COBOLSQL)
            {
                while (callChain.Count > 0 && callChain.Peek().indentCount >= call.indentCount)
                {
                    var popped = callChain.Pop();
                    if (popped.StopLine == 0)
                    {
                        popped.StopLine = stopLineNumber;
                    }
                }
            }

            if (callChain.Count > 0)
            {
                callChain.Peek().Children.Add(call);
                call.Parent = callChain.Peek();
            }
            if (callChain.Count == 0)
            {
                executionCalls.Add(call);
            }
            callChain.Push(call);
        }

        public void ProcessLine(string line, long lineNumber)
        {
            if (0 == 1)
            {
                /*if (contextMarker.IsMatch(line) == false)
                {
                    return;
                }
                var currentContextString = contextMarker.Match(line).Groups[0].Value;*/

                /*var match = callMarker.Match(line);
                if (match.Success)
                {
                    _sqlExecCallCount++;
                    var call = new ExecutionCall() { Context = currentContextString, Type = ExecutionCallType.CALL, StartLine = lineNumber, Function = match.Groups[3].Value + ": " + match.Groups[4].Value, indentCount = match.Groups[2].Value.Length };
                    allCalls.Add(call);
                    call.Duration = Double.Parse(match.Groups[1].Value);
                    if (callChain.Count > 0 && callChain.Peek().indentCount == call.indentCount)
                    {
                        var popped = callChain.Pop();
                        if (popped.StopLine == 0)
                        {
                            popped.StopLine = lineNumber;
                        }
                    }

                    if (callChain.Count > 0 && callChain.Peek().Type == ExecutionCallType.CALL)
                    {
                        while(callChain.Count > 0 && callChain.Peek().indentCount >= call.indentCount)
                        {
                            var popped = callChain.Pop();
                            if (popped.StopLine == 0)
                            {
                                popped.StopLine = lineNumber;
                            }
                        }
                    }

                    if (callChain.Count > 0)
                    {
                        callChain.Peek().Children.Add(call);
                        call.Parent = callChain.Peek();
                    }
                    if (callChain.Count == 0)
                    {
                        executionCalls.Add(call);
                    }
                    callChain.Push(call);
                    return;
                }*/
            }

            if (lineValid.IsMatch(line) == false)
            {
                _prevLine = line;
                return;
            }


            Match m = newStatement.Match(line);

            //if (!m.Success)
            //{
            //    m = cursorCommit.Match(line);
            //}
            if (m.Success)
            {

                if (currentStatement != null)
                {
                    Statements.Add(currentStatement);
                }

                currentStatement = new SQLStatement(m.Groups[4].Value);
                Match mPrev = statementName.Match(_prevLine);
                if (mPrev.Success)
                {
                    currentStatement.Name = mPrev.Groups[2].Value;
                }

                currentStatement.CursorNumber = int.Parse(m.Groups[2].Value);
                currentStatement.Cobol = true;
                currentStatement.Context = "Cursor: " + m.Groups[2].Value + " Line Number: " + m.Groups[1].Value;
                currentStatement.LineNumber = lineNumber;

                //TODO - Make logic better here, assuming that the next index to add is 1 more than current count
                if (sqlStatementForCursor.Count <= int.Parse(m.Groups[2].Value))
                {
                    sqlStatementForCursor.Add(currentStatement);
                }
                else
                {
                    sqlStatementForCursor[int.Parse(m.Groups[2].Value)] = currentStatement;
                }


                _sqlExecCallCount++;
                var call = new ExecutionCall() { Context = "Cursor: " + m.Groups[2].Value + " Line Number: " + m.Groups[1].Value, Type = ExecutionCallType.COBOLSQL, StartLine = lineNumber, Function = m.Groups[4].Value, indentCount = int.Parse(m.Groups[2].Value), SQLStatement = currentStatement };

                addToChain(call, lineNumber);

                _prevLine = line;
                return;
            }

            //Check for cursor Disconecct
            m = cursorDisconnect.Match(line);

            if (m.Success)
            {
                var cursorInt = int.Parse(m.Groups[1].Value);
                if (cursorInt <= sqlStatementForCursor.Count)
                {
                    sqlStatementForCursor[cursorInt] = new SQLStatement();
                }
                return;
            }

            //Check if a new execution of an open cursor
            if (newExecution(line, _prevLine))
            {
                Match mLineCursorNbr = lineAndCursorMarker.Match(line);
                var lineNbrInTrace = "";
                var cursorNbr = "";
                if (mLineCursorNbr.Success)
                {
                    lineNbrInTrace = mLineCursorNbr.Groups[1].Value;
                    cursorNbr = mLineCursorNbr.Groups[2].Value;
                }
                //Find call for this cursor #
                currentStatement = sqlStatementForCursor.ElementAt(int.Parse(cursorNbr));

                _sqlExecCallCount++;
                var call = new ExecutionCall() { Context = "Cursor: " + cursorNbr + " Line Number: " + lineNbrInTrace, Type = ExecutionCallType.COBOLSQL, StartLine = lineNumber, Function = currentStatement.Statement, indentCount = int.Parse(cursorNbr), SQLStatement = currentStatement };

                currentStatement.BindValues.Clear();
                currentStatement.LineNumber = int.Parse(lineNbrInTrace);

                addToChain(call, lineNumber);
            }

            if (0 == 1)
            {
                //m = fetchStatement.Match(line);
                //if (m.Success)
                //{
                //    if (int.Parse(m.Groups[1].Value) != currentStatement.RCNumber)
                //    {
                //        _prevLine = line;
                //        return;
                //    }

                //    currentStatement.FetchCount++;
                //    /* TODO: Pull fetch time? */
                //    /* currentStatement.FetchTime += double.Parse(m.Groups[2].Value); */
                //    _prevLine = line;
                //    return;
                //}
            }

            m = bindStatementType.Match(line);
            if (m.Success)
            {
                SQLBindValue bind = new SQLBindValue();
                bind.Index = int.Parse(m.Groups[2].Value);
                bind.TypeString = m.Groups[3].Value;

                if (m.Groups[3].Value == "SQLPSPD")
                {
                    Match m1 = bindStatementSQLPSPDValue.Match(line);
                    bind.Precision = int.Parse(m1.Groups[1].Value);
                    bind.Scale = int.Parse(m1.Groups[2].Value);
                    bind.Value = m1.Groups[3].Value;
                }
                else
                {
                    Match m1 = bindStatementValue.Match(line);
                    bind.Length = int.Parse(m1.Groups[1].Value);
                    bind.Value = m1.Groups[2].Value;
                }

                currentStatement.BindValues.Add(bind);
                _prevLine = line;
                return;
            }
            
            var match = startMarker.Match(line);

            if (match.Success == false)
            {
                match = resumeMarker.Match(line);
            }
            /* Start marker, or Resume Marker */
            if (match.Success)
            {
                _sqlExecCallCount++;
                // we have the start of a function
                var call = new ExecutionCall() { Context = "", Type = ExecutionCallType.NORMAL, StartLine = lineNumber, Nest = match.Groups[1].Value, Function = match.Groups[2].Value };
                allCalls.Add(call);
                if (callChain.Count == 0)
                {
                    executionCalls.Add(call);
                }
                callChain.Push(call);

                if (callChain.Count > _maxCallDepth)
                {
                    _maxCallDepth = callChain.Count;
                }

                return;
            }

            match = endMarker.Match(line);
            if (match.Success == false)
            {
                match = reendMarker.Match(line);
            }
            /* end marker or reend marker */
            if (match.Success)
            {
                // we've reached the end of a call, we need to find it in the list and mark the ending line
                var nest = match.Groups[1].Value;
                var func = match.Groups[2].Value;
                var dur = match.Groups.Count == 4 ? match.Groups[3].Value : "0";

                bool callFound = false;
                ExecutionCall call = null;
                while (callFound == false)
                {
                    call = callChain.Pop();
                    if (call.Nest == nest && call.Function == func)
                    {
                        callFound = true;
                        call.StopLine = lineNumber;
                        call.Duration = Double.Parse(dur);
                    }

                }

                if (nest.Equals("00") == false && callChain.Count > 0)
                {
                    /* If we are a nested call, and there are calls on the call chain *
                     * then we should associate the current call with its parent      *
                     */
                    var parent = callChain.Peek();
                    parent.Children.Add(call);
                    call.Parent = parent;
                }
                return;
            }

            if (0 == 1)
            {
                //match = startExtMarker.Match(line);
                //if (match.Success)
                //{
                //    _sqlExecCallCount++;
                //    // we have the start of a function
                //    var call = new ExecutionCall() { Context = "", Type = ExecutionCallType.EXTERNAL, StartLine = lineNumber, Nest = match.Groups[1].Value, Function = match.Groups[2].Value };
                //    allCalls.Add(call);
                //    if (callChain.Count == 0)
                //    {
                //        executionCalls.Add(call);
                //    }

                //    /* test */
                //    if (callChain.Count > 0 && callChain.Peek().Type == ExecutionCallType.CALL)
                //    {
                //        var parent = callChain.Pop();
                //        if (parent.StopLine == 0)
                //        {
                //            parent.StopLine = lineNumber;
                //        }
                //        parent.Children.Add(call);
                //        call.Parent = parent;
                //    }

                //    callChain.Push(call);
                //    if (callChain.Count > _maxCallDepth)
                //    {
                //        _maxCallDepth = callChain.Count;
                //    }

                //    return;
                //}

                //match = endExtMarker.Match(line);
                //if (match.Success)
                //{
                //    // we've reached the end of a call, we need to find it in the list and mark the ending line
                //    var nest = match.Groups[1].Value;
                //    var func = match.Groups[2].Value;
                //    var dur = match.Groups[3].Value;

                //    if (callChain.Count > 0 && callChain.Peek().Type == ExecutionCallType.CALL)
                //    {
                //        while (callChain.Peek().Type == ExecutionCallType.CALL || callChain.Peek().Nest != nest)
                //        {
                //            var popped = callChain.Pop();
                //            if (popped.StopLine == 0)
                //            {
                //                popped.StopLine = lineNumber;
                //            }
                //        }
                //    }

                //    //var call = executionCalls.Where(p => p.Context.Equals(currentContextString) && p.Nest.Equals(nest) && p.Function.Equals(func) && p.StopLine == 0).First<ExecutionCall>();
                //    var call = callChain.Pop();
                //    call.StopLine = lineNumber;
                //    call.Duration = Double.Parse(dur);
                //}

                //match = sqlStatement.Match(line);
                //if (match.Success)
                //{
                //    var sqlCall = new ExecutionCall() {Context= "", Type = ExecutionCallType.SQL, StartLine = lineNumber, StopLine = lineNumber, Function = "SQL" };
                //    allCalls.Add(sqlCall);
                //    if (callChain.Count > 0)
                //    {
                //        sqlCall.Parent = callChain.Peek();
                //        callChain.Peek().Children.Add(sqlCall);
                //    } else
                //    {
                //        executionCalls.Add(sqlCall);
                //    }
                //    sqlCalls.Add(sqlCall);
                //    return;
                //}
                //match = ppcExceptionStatement.Match(line);
                //if (match.Success)
                //{
                //    _sqlExceptionCount++;
                //    var exception = new PPCException() { Message = match.Groups[1].Value };
                //    if (callChain.Count > 0)
                //    {
                //        var call = callChain.Peek();
                //        call.PPCException = exception;
                //        call.IsError = true;
                //        var parent = call.Parent;
                //        while (parent != null)
                //        {
                //            parent.HasError = true;
                //            parent = parent.Parent;
                //        }
                //    }


                //}
            }

            _prevLine = line;
            return;
        }

    }

}
