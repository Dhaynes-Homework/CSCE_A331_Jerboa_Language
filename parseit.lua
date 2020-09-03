-- parseit.lua
-- Devan Haynes
-- Based on Glenn G. Chappell rdparser4.lua program
-- Updated: 11 Mar 2019
--
-- For CS F331 / CSCE A331 Spring 2019
-- Recursive-Descent Parser
-- Requires lexit.lua


-- Grammar
-- Start symbol: program
--

--    	program	  →  	stmt_list
--    	stmt_list	  →  	{ statement }
--    	statement	  →  	‘write’ ‘(’ write_arg { ‘,’ write_arg } ‘)’
--    	 	|  	‘def’ ID ‘(’ ‘)’ stmt_list ‘end’
--    	 	|  	‘if’ expr stmt_list { ‘elseif’ expr stmt_list } [ ‘else’ stmt_list ] ‘end’
--    	 	|  	‘while’ expr stmt_list ‘end’
--    	 	|  	‘return’ expr
--    	 	|  	ID ( ‘(’ ‘)’ | [ ‘[’ expr ‘]’ ] ‘=’ expr )
--    	write_arg	  →  	‘cr’
--    	 	|  	STRLIT
--    	 	|  	expr
--    	expr	  →  	comp_expr { ( ‘&&’ | ‘||’ ) comp_expr }
--    	comp_expr	  →  	‘!’ comp_expr
--    	 	|  	arith_expr { ( ‘==’ | ‘!=’ | ‘<’ | ‘<=’ | ‘>’ | ‘>=’ ) arith_expr }
--    	arith_expr	  →  	term { ( ‘+’ | ‘-’ ) term }
--    	term	  →  	factor { ( ‘*’ | ‘/’ | ‘%’ ) factor }
--    	factor	  →  	‘(’ expr ‘)’
--    	 	|  	( ‘+’ | ‘-’ ) factor
--    	 	|  	NUMLIT
--    	 	|  	( ‘true’ | ‘false’ )
--    	 	|  	‘readnum’ ‘(’ ‘)’
--    	 	|  	ID [ ‘(’ ‘)’ | ‘[’ expr ‘]’ ]
--
-- Usage:
--    Used for assignment 4
--    used to parse based on assignment 4 parsing specifications


local parseit = {}  -- Our module

local lexit = require "lexit"


-- Variables

-- For lexer iteration
local iter          -- Iterator returned by lexit.lex
local state         -- State for above iterator (maybe not used)
local lexit_out_s   -- Return value #1 from above iterator
local lexit_out_c   -- Return value #2 from above iterator

-- For current lexeme
local lexstr = ""   -- String form of current lexeme
local lexcat = 0    -- Category of current lexeme:
                    --  one of categories below, or 0 for past the end


-- Symbolic Constants for AST

local STMT_LIST    = 1
local WRITE_STMT   = 2
local FUNC_DEF     = 3
local FUNC_CALL    = 4
local IF_STMT      = 5
local WHILE_STMT   = 6
local RETURN_STMT  = 7
local ASSN_STMT    = 8
local CR_OUT       = 9
local STRLIT_OUT   = 10
local BIN_OP       = 11
local UN_OP        = 12
local NUMLIT_VAL   = 13
local BOOLLIT_VAL  = 14
local READNUM_CALL = 15
local SIMPLE_VAR   = 16
local ARRAY_VAR    = 17


-- Utility Functions

-- advance
-- Go to next lexeme and load it into lexstr, lexcat.
-- Should be called once before any parsing is done.
-- Function init must be called before this function is called.
local function advance()
    -- Advance the iterator
    lexit_out_s, lexit_out_c = iter(state, lexit_out_s)

    -- If we're not past the end, copy current lexeme into vars
    if lexit_out_s ~= nil then
        lexstr, lexcat = lexit_out_s, lexit_out_c
    else
        lexstr, lexcat = "", 0
    end
end


-- init
-- Initial call. Sets input for parsing functions.
local function init(prog)
    iter, state, lexit_out_s = lexit.lex(prog)
    advance()
end


-- atEnd
-- Return true if pos has reached end of input.
-- Function init must be called before this function is called.
local function atEnd()
    return lexcat == 0
end


-- matchString
-- Given string, see if current lexeme string form is equal to it. If
-- so, then advance to next lexeme & return true. If not, then do not
-- advance, return false.
-- Function init must be called before this function is called.
local function matchString(s)
    if lexstr == s then
        advance()
        return true
    else
        return false
    end
end


-- matchCat
-- Given lexeme category (integer), see if current lexeme category is
-- equal to it. If so, then advance to next lexeme & return true. If
-- not, then do not advance, return false.
-- Function init must be called before this function is called.
local function matchCat(c)
    if lexcat == c then
        advance()
        return true
    else
        return false
    end
end


-- Primary Function for Client Code

-- "local" statements for parsing functions
local parse_program
local parse_stmt_list
local parse_statement
local parse_write_arg
local parse_expr
local parse_comp_expr
local parse_arith_expr
local parse_term
local parse_factor

-- parse
-- Given program, initialize parser and call parsing function for start
-- symbol. Returns pair of booleans & AST. First boolean indicates
-- successful parse or not. Second boolean indicates whether the parser
-- reached the end of the input or not. AST is only valid if first
-- boolean is true.
function parseit.parse(prog)
    -- Initialization
    init(prog)

    -- Get results from parsing
    local good, ast = parse_program()  -- Parse start symbol
    local done = atEnd()

    -- And return them
    return good, done, ast
end



-- Parsing Functions

-- Each of the following is a parsing function for a nonterminal in the
-- grammar. Each function parses the nonterminal in its name and returns
-- a pair: boolean, AST. On a successul parse, the boolean is true, the
-- AST is valid, and the current lexeme is just past the end of the
-- string the nonterminal expanded into. Otherwise, the boolean is
-- false, the AST is not valid, and no guarantees are made about the
-- current lexeme. See the AST Specification near the beginning of this
-- file for the format of the returned AST.

-- NOTE. Declare parsing functions "local" above, but not below. This
-- allows them to be called before their definitions.



-- parse_program
-- Parsing function for nonterminal "program".
-- Function init must be called before this function is called.
function parse_program()
    local good, ast

    good, ast = parse_stmt_list()
    return good, ast
end


-- parse_stmt_list
-- Parsing function for nonterminal "stmt_list".
-- Function init must be called before this function is called.
function parse_stmt_list()
    local good, ast, newast

    ast = { STMT_LIST }
    while true do
        if lexstr ~= "write"
          and lexstr ~= "def"
          and lexstr ~= "if"
          and lexstr ~= "while"
          and lexstr ~= "return"
          and lexcat ~= lexit.ID then
            return true, ast
        end

        good, newast = parse_statement()
        if not good then
            return false, nil
        end

        table.insert(ast, newast)
    end
end


-- parse_statement
-- Parsing function for nonterminal "statement".
-- Function init must be called before this function is called.
function parse_statement()
    local good, ast1, ast2, savelex

    if matchString("write") then
        if not matchString("(") then
            return false, nil
        end

        good, ast1 = parse_write_arg()
        if not good then
            return false, nil
        end

        ast2 = { WRITE_STMT, ast1 }

        while matchString(",") do
            good, ast1 = parse_write_arg()
            if not good then
                return false, nil
            end

            table.insert(ast2, ast1)
        end

        if not matchString(")") then
            return false, nil
        end

        return true, ast2

    elseif matchString('end') then
        return true, ast1
    elseif matchString("def") then
        if lexstr == 'end' then
          return false, nil
        end
        
        local tempstr
        tempstr = lexstr
        
        if matchCat(lexit.ID) then
          ast1 = { FUNC_DEF, tempstr }
          if not matchString("(") then
              return false, nil
          end
          if not matchString(")") then
              return false, nil
          end
          good, ast2 = parse_stmt_list()
          if not good then
            return false, nil
          end
          
          if not matchString('end') then
            return false, nil
          end
          table.insert(ast1, ast2)
          return true, ast1
        end
    elseif matchString("while") then
        ast1 = { WHILE_STMT }
        good, ast2 = parse_expr()
        if not good then
            return false, nil
        end
        table.insert(ast1, ast2)
        good, ast2 = parse_stmt_list()
        if not good then
            return false, nil
        end
        if not matchString('end') then
            return false, nil
        end
        table.insert(ast1, ast2)
        return true, ast1
    elseif matchString("if") then
        ast1 = { IF_STMT }
        good, ast2 = parse_expr()
        if not good then
          return false, nil
        end
        table.insert(ast1, ast2)
        good, ast2 = parse_stmt_list()
        if not good then
          return false, nil
        end
        table.insert(ast1, ast2)
        while matchString('elseif') do
          good, ast2 = parse_expr()
          if not good then
            return false, nil
          end
          table.insert(ast1, ast2)
          good, ast2 = parse_stmt_list()
          if not good then
            return false, nil
          end
          table.insert(ast1, ast2)
        end
        if matchString('else') then
          good, ast2 = parse_stmt_list()
          if not good then
            return false, nil
          end
          table.insert(ast1, ast2)
        end
        if not matchString('end') then
            return false, nil
        end
        return true, ast1
    elseif matchString('return') then
        good, ast2 = parse_expr()
        if not good then
            return false, nil
        end
        ast1 = {RETURN_STMT, ast2}
        return true, ast1
      
    elseif lexcat == lexit.ID then
        local tempstr
        tempstr = lexstr
        advance()
        if matchString('(') then
          ast1 = { FUNC_CALL, tempstr }
          if not matchString(")") then
            return false, nil
          end
          return true, ast1
        elseif matchString('=') then
          ast1 = { ASSN_STMT, {SIMPLE_VAR, tempstr} }
          good, ast2 = parse_expr()
          if not good then
            return false, nil
          end
          table.insert(ast1, ast2)
          return true, ast1
        elseif matchString('[') then
          good, ast2 = parse_expr()
          if not good then
            return false, nil
          end
          if not matchString("]") then
            return false, nil
          end
          if matchString('=') then
            ast1 = { ASSN_STMT , { ARRAY_VAR , tempstr , ast2}}
            good, ast2 = parse_expr()
            if not good then
              return false, nil
            end
            table.insert(ast1, ast2)
            return true, ast1
          end
          
          
        end
        
        return false, nil
        
    end
      
advance()  -- Temporary fix ??
-- return false, nil  -- Might not need
end


-- parse_write_arg()
-- Parsing function for nonterminal "write_arg"
-- Function init must be called before this function is called.
function parse_write_arg()
  local good, ast
  if lexcat == lexit.STRLIT then
    ast = { STRLIT_OUT, lexstr }
    advance()
    return true, ast
  elseif matchString('cr') then
    ast = { CR_OUT }
    return true , ast
  elseif lexcat == lexit.KEY then
    return false, nil
  else
    good, ast = parse_expr()
    if not good then
        return false, nil
    end
    return true, ast
  end
  
end


-- parse_expr
-- Parsing function for nonterminal "expr".
-- Function init must be called before this function is called.
function parse_expr()
    local good, ast, saveop, newast

    good, ast = parse_comp_expr()
    if not good then
        return false, nil
    end

    while true do
        saveop = lexstr
        if not matchString("&&") and not matchString("||") then
            break
        end

        good, newast = parse_comp_expr()
        if not good then
            return false, nil
        end

        ast = { { BIN_OP, saveop }, ast, newast }
    end

    return true, ast
end


-- parse_comp_expr
-- Parsing function for nonterminal "comp_expr".
-- Function init must be called before this function is called.
function parse_comp_expr()
    local good, ast, saveop, newast
    
    if matchString('!') then
      good, ast = parse_comp_expr()
      if not good then
        return false, nil
      end
      ast = {{UN_OP, '!'} , ast}
      return true, ast
    end
    
    good, ast = parse_arith_expr()
    if not good then
        return false, nil
    end

    while true do
        saveop = lexstr
        if not matchString("==") and not matchString("!=") and not matchString("<") and not matchString(">") and not matchString("<=") and not matchString(">=") then
            break
        end

        good, newast = parse_arith_expr()
        if not good then
            return false, nil
        end

        ast = { { BIN_OP, saveop }, ast, newast }
    end

    return true, ast
end


-- parse_arith_expr
-- Parsing function for nonterminal "arith_expr".
-- Function init must be called before this function is called.
function parse_arith_expr()
    local good, ast, saveop, newast

    good, ast = parse_term()
    if not good then
        return false, nil
    end

    while true do
        saveop = lexstr
        if not matchString("+") and not matchString("-") then
            break
        end

        good, newast = parse_term()
        if not good then
            return false, nil
        end

        ast = { { BIN_OP, saveop }, ast, newast }
    end

    return true, ast
end


-- parse_term
-- Parsing function for nonterminal "term".
-- Function init must be called before this function is called.
function parse_term()
    local good, ast, saveop, newast

    good, ast = parse_factor()
    if not good then
        return false, nil
    end

    while true do
        saveop = lexstr
        if not matchString("*") and not matchString("/") and not matchString("%") then
            break
        end

        good, newast = parse_factor()
        if not good then
            return false, nil
        end

        ast = { { BIN_OP, saveop }, ast, newast }
    end

    return true, ast
end


-- parse_factor
-- Parsing function for nonterminal "factor".
-- Function init must be called before this function is called.
function parse_factor()
    local savelex, good, ast

    savelex = lexstr
    if matchCat(lexit.ID) then
        if matchString('(') then
          ast = { FUNC_CALL, savelex }
          if not matchString(")") then
            return false, nil
          end
          return true, ast
        elseif matchString('[') then
          good, ast = parse_expr()
          if not good then
            return false, nil
          end
          if not matchString("]") then
            return false, nil
          end
          return true, { ARRAY_VAR , savelex , ast}
        else
          return true, { SIMPLE_VAR, savelex }
        end
        
    elseif matchCat(lexit.NUMLIT) then
        return true, { NUMLIT_VAL, savelex }
    elseif matchString('readnum') then
        if matchString('(') then
          if not matchString(")") then
            return false, nil
          end
          return true, {READNUM_CALL}
        end
    elseif matchString('+') or matchString('-') then
        good, ast = parse_factor()
        if not good then
            return false, nil
        end
        ast = {{ UN_OP, savelex }, ast}
        return true, ast
    elseif matchString('true') or matchString('false') then
        return true, { BOOLLIT_VAL, savelex }
    elseif matchString("(") then
        good, ast = parse_expr()
        if not good then
            return false, nil
        end

        if not matchString(")") then
            return false, nil
        end

        return true, ast
    else
        return false, nil
    end
end
  


-- Module Export

return parseit

