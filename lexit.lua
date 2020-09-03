-- lexit.lua
-- Devan Haynes
-- Based on Glenn G. Chappell lexer.lua program
-- Started: 17 Feb 2019
-- Updated: 20 Feb 2019
--
-- For CSCE A331 Spring 2019

-- Usage:
--    Used for assignment 3
--    used to lex based on assignment 3 lexer specifications


-- *********************************************************************
-- Module Table Initialization
-- *********************************************************************


local lexit = {}  -- Our module; members are added below


-- *********************************************************************
-- Public Constants
-- *********************************************************************


-- Numeric constants representing lexeme categories
lexit.KEY    = 1
lexit.ID     = 2
lexit.NUMLIT = 3
lexit.STRLIT = 4
lexit.OP     = 5
lexit.PUNCT  = 6
lexit.MAL    = 7


-- catnames
-- Array of names of lexeme categories.
-- Human-readable strings. Indices are above numeric constants.
lexit.catnames = {
    "Keyword",
    "Identifier",
    "NumericLiteral",
    "StringLiteral",
    "Operator",
    "Punctuation",
    "Malformed"
}


-- *********************************************************************
-- Kind-of-Character Functions
-- *********************************************************************

-- All functions return false when given a string whose length is not
-- exactly 1.


-- isLetter
-- Returns true if string c is a letter character, false otherwise.
local function isLetter(c)
    if c:len() ~= 1 then
        return false
    elseif c >= "A" and c <= "Z" then
        return true
    elseif c >= "a" and c <= "z" then
        return true
    else
        return false
    end
end


-- isDigit
-- Returns true if string c is a digit character, false otherwise.
local function isDigit(c)
    if c:len() ~= 1 then
        return false
    elseif c >= "0" and c <= "9" then
        return true
    else
        return false
    end
end


-- isWhitespace
-- Returns true if string c is a whitespace character, false otherwise.
local function isWhitespace(c)
    if c:len() ~= 1 then
        return false
    elseif c == " " or c == "\t" or c == "\n" or c == "\r"
      or c == "\f" then
        return true
    else
        return false
    end
end


-- isIllegal
-- Returns true if string c is an illegal character, false otherwise.
local function isIllegal(c)
    if c:len() ~= 1 then
        return false
    elseif isWhitespace(c) then
        return false
    elseif c >= " " and c <= "~" then
        return false
    else
        return true
    end
end


-- *********************************************************************
-- The lexit
-- *********************************************************************


-- lex
-- Our lexit
-- Intended for use in a for-in loop:
--     for lexstr, cat in lexit.lex(program) do
-- Here, lexstr is the string form of a lexeme, and cat is a number
-- representing a lexeme category. (See Public Constants.)
function lexit.lex(program)
    -- ***** Variables (like class data members) *****

    local pos       -- Index of next character in program
                    -- INVARIANT: when getLexeme is called, pos is
                    --  EITHER the index of the first character of the
                    --  next lexeme OR program:len()+1
    local state     -- Current state for our state machine
    local ch        -- Current character
    local lexstr    -- The lexeme, so far
    local category  -- Category of lexeme, set when state set to DONE
    local handlers  -- Dispatch table; value created later

    -- ***** States *****

    local DONE   = 0
    local START  = 1
    local LETTER = 2
    local DIGIT  = 3
    local DIGEXP = 4
    local DBLQUT = 5
    local PLUS   = 6
    local MINUS  = 7
    local STAR   = 8
    local SGLQUT = 9

    -- ***** Character-Related Utility Functions *****

    -- currChar
    -- Return the current character, at index pos in program. Return
    -- value is a single-character string, or the empty string if pos is
    -- past the end.
    local function currChar()
        return program:sub(pos, pos)
    end

    -- nextChar
    -- Return the next character, at index pos+1 in program. Return
    -- value is a single-character string, or the empty string if pos+1
    -- is past the end.
    local function nextChar()
        return program:sub(pos+1, pos+1)
    end
    
    local function next2Char()
        return program:sub(pos+2, pos+2)
    end
    
    local function prevChar()
        return program:sub(pos-1, pos-1)
    end
    local function prev4Char()
        return program:sub(pos-4, pos-4)
    end


    -- drop1
    -- Move pos to the next character.
    local function drop1()
        pos = pos+1
    end

    -- add1
    -- Add the current character to the lexeme, moving pos to the next
    -- character.
    local function add1()
        lexstr = lexstr .. currChar()
        drop1()
    end

    -- skipWhitespace
    -- Skip whitespace and comments, moving pos to the beginning of
    -- the next lexeme, or to program:len()+1.
    local function skipWhitespace() -- FIX THIS SO COMMENT IS #
        while true do      -- In whitespace
            while isWhitespace(currChar()) do
                drop1()
            end

            if currChar() ~= "#" then  -- Comment?
                break
            end
            drop1()

            while true do  -- In comment
                if currChar() == "\n" then
                    drop1()
                    --drop1()
                    break
                elseif currChar() == "" then  -- End of input?
                   return
                end
                drop1()
            end
        end
    end

    -- ***** State-Handler Functions *****

    -- A function with a name like handle_XYZ is the handler function
    -- for state XYZ

    local function handle_DONE()
        io.write("ERROR: 'DONE' state should not be handled\n")
        assert(0)
    end

    local function handle_START()
        if isIllegal(ch) then
            add1()
            state = DONE
            category = lexit.MAL
        elseif isLetter(ch) or ch == "_" then
            add1()
            state = LETTER
        elseif isDigit(ch) then
            add1()
            state = DIGIT
        elseif ch == "+" then
            state = PLUS
        elseif ch == "-" then
            state = MINUS
        elseif ch == "*" or ch == "/" or ch == "=" or ch == "[" or ch == "]" or ch == "%" or ch == ">" or
               ch == "<" or ch == "!" or (ch == "&" and nextChar() == "&") or (ch == "|" and nextChar() == "|") then
            add1()
            state = STAR
        elseif ch == [["]] then
            add1()
            state = DBLQUT
        elseif ch == [[']] then
            add1()
            state = SGLQUT
        else
            add1()
            state = DONE
            category = lexit.PUNCT
        end
    end

    local function handle_LETTER()
        if isLetter(ch) or isDigit(ch) or ch == "_" then
            add1()
        else
            state = DONE
            if lexstr == "begin" or lexstr == "end" or lexstr == "print" or lexstr == "cr" or lexstr == "def"
              or lexstr == "else" or lexstr == "elseif" or lexstr == "end" or lexstr == "false" or lexstr == "if"
              or lexstr == "readnum" or lexstr == "return" or lexstr == "true" or lexstr == "while" 
              or lexstr == "write" then
                category = lexit.KEY
            else
                category = lexit.ID
            end
        end
    end

    local function handle_DIGIT()
        if isDigit(ch) then
            add1()
        elseif (ch == "e" or ch == "E") and (nextChar() == "+") and (isDigit(next2Char())) then
            add1()
            add1()
            add1()
            state = DIGEXP
        elseif (ch == "e" or ch == "E") and isDigit(nextChar()) then
            add1()
            add1()
            state = DIGEXP
        else
            state = DONE
            category = lexit.NUMLIT
        end
    end

    local function handle_DIGEXP()
        if isDigit(ch) then
            add1()
        else
            state = DONE
            category = lexit.NUMLIT
        end
    end

    local function handle_DBLQUT()
        if ch == [["]] then
            add1()
            state = DONE
            category = lexit.STRLIT
        elseif ch == "" then
            state = DONE
            category = lexit.MAL
        elseif ch == "\n" then
            add1()
            state = DONE
            category = lexit.MAL
        else
          add1()
        end
    end
    
    local function handle_SGLQUT()
        if ch == [[']] then
            add1()
            state = DONE
            category = lexit.STRLIT
        elseif ch == "" then
            state = DONE
            category = lexit.MAL
        elseif ch == "\n" then
            add1()
            state = DONE
            category = lexit.MAL
        else
          add1()
        end
    end
      

    local function handle_PLUS()
        if ch == "+" and (isLetter(prevChar()) or isWhitespace(prevChar())) and category == lexit.ID then
            add1()
            state = DONE
            category = lexit.OP
        elseif ch == "+" and (isDigit(prevChar()) or isWhitespace(prevChar())) and category == lexit.NUMLIT then
            add1()
            state = DONE
            category = lexit.OP
        elseif ch == "+" and prevChar() == "]" and category == lexit.OP then
            add1()
            state = DONE
            category = lexit.OP
        elseif ch == "+" and prevChar() == ")" and category == lexit.PUNCT then
            add1()
            state = DONE
            category = lexit.OP
        elseif ch == "+" and prevChar() == "e" and (prev4Char() == "t" or prev4Char() == "a") and category == lexit.KEY then
            add1()
            state = DONE
            category = lexit.OP
        elseif ch == "+" and isDigit(nextChar()) then
            add1()
            add1()
            state = DIGIT
        elseif ch == "+" or ch == "=" then
            add1()
            state = DONE
            category = lexit.OP
        elseif isDigit(ch) then
            add1()
            state = DIGIT
        else
            state = DONE
            category = lexit.OP
        end
    end

    local function handle_MINUS()
        if ch == "-" and (isLetter(prevChar()) or isWhitespace(prevChar())) and category == lexit.ID then
            add1()
            state = DONE
            category = lexit.OP
        elseif ch == "-" and (isDigit(prevChar()) or isWhitespace(prevChar())) and category == lexit.NUMLIT then
            add1()
            state = DONE
            category = lexit.OP
        elseif ch == "-" and prevChar() == "]" and category == lexit.OP then
            add1()
            state = DONE
            category = lexit.OP
        elseif ch == "-" and prevChar() == ")" and category == lexit.PUNCT then
            add1()
            state = DONE
            category = lexit.OP
        elseif ch == "-" and prevChar() == "e" and (prev4Char() == "t" or prev4Char() == "a") and category == lexit.KEY then
            add1()
            state = DONE
            category = lexit.OP
        elseif ch == "-" and isDigit(nextChar()) then
            add1()
            add1()
            state = DIGIT
        elseif ch == "-" or ch == "=" then
            add1()
            state = DONE
            category = lexit.OP
        elseif isDigit(ch) then
            add1()
            state = DIGIT
        else
            state = DONE
            category = lexit.OP
        end
    end

    local function handle_STAR()
        if ch == "=" and (prevChar() == "=" or prevChar() == ">" or prevChar() == "<" or prevChar() == "!") then
            add1()
            state = DONE
            category = lexit.OP
        elseif ch == "&" and prevChar() == "&" then
            add1()
            state = DONE
            category = lexit.OP
        elseif ch == "|" and prevChar() == "|" then
            add1()
            state = DONE
            category = lexit.OP
        else
            state = DONE
            category = lexit.OP
        end
    end

    -- ***** Table of State-Handler Functions *****

    handlers = {
        [DONE]=handle_DONE,
        [START]=handle_START,
        [LETTER]=handle_LETTER,
        [DIGIT]=handle_DIGIT,
        [DIGEXP]=handle_DIGEXP,
        [SGLQUT]=handle_SGLQUT,
        [PLUS]=handle_PLUS,
        [MINUS]=handle_MINUS,
        [STAR]=handle_STAR,
        [DBLQUT]=handle_DBLQUT
    }

    -- ***** Iterator Function *****

    -- getLexeme
    -- Called each time through the for-in loop.
    -- Returns a pair: lexeme-string (string) and category (int), or
    -- nil, nil if no more lexemes.
    local function getLexeme(dummy1, dummy2)
        if pos > program:len() then
            return nil, nil
        end
        lexstr = ""
        state = START
        while state ~= DONE do
            ch = currChar()
            handlers[state]()
        end

        skipWhitespace()
        return lexstr, category
    end

    -- ***** Body of Function lex *****

    -- Initialize & return the iterator function
    pos = 1
    skipWhitespace()
    return getLexeme, nil, nil
end


-- *********************************************************************
-- Module Table Return
-- *********************************************************************


return lexit

