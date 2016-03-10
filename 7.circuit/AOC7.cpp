// Circuit_AOC7.cpp : Defines the entry point for the console application.
//

#ifdef PC
#include "stdafx.h"
#endif

/*
--- Advent of Code Day 7: Some Assembly Required ---

This year, Santa brought little Bobby Tables a set of wires and bitwise
logic gates! Unfortunately, little Bobby is a little under the
recommended age range, and he needs help assembling the circuit.

Each wire has an identifier (some lowercase letters) and can carry a
16-bit signal (a number from 0 to 65535). A signal is provided to each
wire by a gate, another wire, or some specific value. Each wire can only
get a signal from one source, but can provide its signal to multiple
destinations. A gate provides no signal until all of its inputs have a
signal.

The included instructions booklet describes how to connect the parts
together: x AND y -> z means to connect wires x and y to an AND gate,
and then connect its output to wire z.

For example:

123 -> x means that the signal 123 is provided to wire x.
x AND y -> z means that the bitwise AND of wire x and wire y is provided
to wire z.

p LSHIFT 2 -> q means that the value from wire p is left-shifted by 2
and then provided to wire q.

NOT e -> f means that the bitwise complement of the value from wire e is
provided to wire f.

Other possible gates include OR (bitwise OR) and RSHIFT (right-shift).
If, for some reason, you'd like to emulate the circuit instead, almost
all programming languages (for example, C, JavaScript, or Python)
provide operators for these gates.

For example, here is a simple circuit:

123 -> x
456 -> y
x AND y -> d
x OR y -> e
x LSHIFT 2 -> f
y RSHIFT 2 -> g
NOT x -> h
NOT y -> i

After it's run, these are the signals on the wires:

d: 72
e: 507
f: 492
g: 114
h: 65412
i: 65079
x: 123
y: 456

In little Bobby's kit's instructions booklet (provided as your puzzle
input), what signal is ultimately provided to wire a?

*/

////////////////////////////////////////////////////////////////////////////////
/*! \file       string_tokeniser.h
\brief      Header file for string_tokeniser class
\author     Orjan Westin [ orjan@coolcowstudio.co.uk ]
\version    1.0
\date       2012
\copyright  BSD (see EOF comment)
Download:   http://coolcowstudio.co.uk/software/source/cpp/utilities.zip
*///////////////////////////////////////////////////////////////////////////////

#ifndef COCOST_STRING_TOKENISER_H_
#define COCOST_STRING_TOKENISER_H_

#include <string>
#include <vector>

//! Cool Cow Studio namespace
namespace CoCoSt
{
	//! Utility function namespace
	namespace Utilities
	{
		//! String tokeniser class
		/*! Class to find and extract tokens from string cheaply and
		non-destructively, using non-fixed delimiters, like strtok.
		Stores a const reference to the string to search, which means that if
		this string is modified between token searches, the search is invalid
		and the tokeniser needs to be reset.
		*/
		class string_tokeniser
		{
			// The string we're searching in
			const std::string& source_;
			// Current location in string
			std::string::size_type current_;
			// Location to start next search
			std::string::size_type next_;
			// Length of current string
			std::string::difference_type length_;
			// Flag indicating whether to include empty strings
			bool empty_;

			// Helper - handle the result of a search, advancing to prepare for next
			template <typename T>
			bool handle_next(size_t advance, const T& separator);

		public:
			//! Constructor
			/*! Constructor, setting the string to work on
			After construction, a call to next() is required to find the first token
			\param source string to work on
			\param empty if true, next() will yield empty strings between two separators
			*/
			string_tokeniser(const std::string& source, bool empty = false);

			//! Advance to next token
			/*! Advance to next token, by given character separator
			E.g "Smith&Jones", separated by '&' gives "Smith", then "Jones"
			\param separator character indicating end of token
			\return true if there is a token to get after the call
			*/
			bool next(const std::string::value_type& separator);

			//! Advance to next token
			/*! Advance to next token, by given string separator
			E.g "Smith and Jones", separated by " and " gives "Smith", then "Jones"
			\param separator string indicating end of token
			\return true if there is a token to get after the call
			*/
			bool next(const std::string& separator);

			//! Advance to next token
			/*! Advance to next token, by given separator
			E.g "Smith & Jones", separated by {'&',' ','-'} gives "Smith", then "Jones"
			(if empty flag not set in construction - otherwise two empty strings are
			found between the two names).
			\param separators characters that can indicate end of token
			\return true if there is a token to get after the call
			*/
			bool next(const std::vector<char>& separators);

			//! Get current token
			/*! Get current token, if any, safely
			\param token string to populate with current token, if any
			\return true if a token was available
			*/
			bool get_token(std::string& token) const;

			//! Get current token
			/*! Get current token, if any, otherwise an empty token
			\return current token, if any, otherwise an empty string
			*/
			std::string get_token() const;

			//! Reset search
			/*! Reset search so the string can be searched from the beginning.
			Required if the string has been modified between calls to next.
			*/
			void reset();

			//! Check token availability
			/*! Check if a token is available
			/return true if there is a current token
			*/
			bool has_token() const;

			//! Check if search is at end
			/*! Check if search is at end
			/return true if no further searches can be done
			*/
			bool at_end() const;

			//! Get source string
			/*! Get source string
			\return reference to source string
			*/
			const std::string& get_source() const;
		};
	}
}

#endif // COCOST_STRING_TOKENISER_H_

/*
Copyright (c) 2012, Orjan Westin
All rights reserved.

Redistribution and use in source and binary forms, with or without modification,
are permitted provided that the following conditions are met:

Redistributions of source code must retain the above copyright notice, this list
of conditions and the following disclaimer.

Redistributions in binary form must reproduce the above copyright notice, this
list of conditions and the following disclaimer in the documentation and/or
other materials provided with the distribution.

The name of the contributor(s) may be used to endorse or promote products derived
from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*/


////////////////////////////////////////////////////////////////////////////////
/*! \file       string_tokeniser.cpp
\brief      Implementation file for string_tokeniser class
\author     Orjan Westin [ orjan@coolcowstudio.co.uk ]
\version    1.0
\date       2012
\copyright  BSD (see EOF comment)
Download:   http://coolcowstudio.co.uk/software/source/cpp/utilities.zip
*///////////////////////////////////////////////////////////////////////////////

// #include "string_tokeniser.h"

namespace CoCoSt
{
	namespace Utilities
	{
		// Constructor
		string_tokeniser::string_tokeniser(const std::string& source, bool empty /*= false*/)
			: source_(source)
			, current_(std::string::npos)
			, next_(source.empty() ? std::string::npos : 0)
			, length_(0)
			, empty_(empty)
		{}

		// Advance to next token
		bool string_tokeniser::next(const std::string::value_type& separator)
		{
			// Store the start
			current_ = next_;
			if (at_end())
				return false;
			// Find next
			next_ = source_.find(separator, current_);
			// Deal with result of search
			return handle_next(1, separator);
		}

		// Advance to next token
		bool string_tokeniser::next(const std::string& separator)
		{
			// Store the start
			current_ = next_;
			if (at_end())
				return false;
			// Find next
			next_ = source_.find(separator, current_);
			// Deal with result of search
			return handle_next(separator.size(), separator);
		}

		// Advance to next token
		bool string_tokeniser::next(const std::vector<char>& separators)
		{
			// Store the start
			current_ = next_;
			if (at_end())
				return false;
			// Find next
			next_ = source_.find_first_of(&separators[0], current_, separators.size());
			// Deal with result of search
			return handle_next(1, separators);
		}

		// Get current token, if any, safely
		bool string_tokeniser::get_token(std::string& token) const
		{
			if (!has_token())
				return false;
			if (0 == length_)
				token.clear();
			else
				token = source_.substr(current_, length_);
			return true;
		}

		// Get current token, if any, otherwise an empty token
		std::string string_tokeniser::get_token() const
		{
			if (!has_token() || (0 == length_))
				return std::string();
			return source_.substr(current_, length_);
		}

		// Reset search so it can be restarted
		void string_tokeniser::reset()
		{
			current_ = std::string::npos;
			next_ = source_.empty() ? std::string::npos : 0;
			length_ = 0;
		}

		// Return true if there is a current token
		bool string_tokeniser::has_token() const
		{
			// Not worried about length here, as it might be an empty token
			return (std::string::npos != current_);
		}

		// Return true if no further searches can be done
		bool string_tokeniser::at_end() const
		{
			return (std::string::npos == next_);
		}

		// Get source string
		const std::string& string_tokeniser::get_source() const
		{
			return source_;
		}

		////////////////////////////////////////////////////////////////////////////
		// Helper

		// Handle the result of a search, advancing to prepare for next search
		template <typename T>
		bool string_tokeniser::handle_next(size_t advance, const T& separator)
		{
			if (std::string::npos == next_)
			{
				// Separator not found, but there might still be data, at the end 
				length_ = source_.size() - current_;
			}
			else
			{
				// Store the length of the current token
				length_ = next_ - current_;
				// and move next starting point to beyond the one we found
				next_ += advance;
				// In the case of double separators (e.g. | in "a|b||d"), this gives an 
				// empty token. If empties aren't accepted, we'll recurse
				if ((0 == length_) && !empty_)
				{
					return next(separator);
				}
			}
			// Do we have a token?
			if (0 < length_)
				return true;
			// Even if empties are accepted, dismiss an empty token at the end of a 
			// string (e.g. "a|b|" gives "a" and "b" only)
			if (!empty_ || (std::string::npos == next_))
			{
				// Invalidate current, so extraction isn't valid
				current_ = next_;
				return false;
			}
			return true;
		}
	}
}

/************ end of Tokeniser stuff ************/

using namespace std;
using namespace CoCoSt;
using namespace CoCoSt::Utilities;

#include <string>
#include <unordered_map>

#include <iostream>
#include <fstream>

#include <cassert>

/************************ Our token stuff *************************/
enum TokType { nott, assign, andd, orr, lshift, rshift, identifier, number, end_of_line };

struct Token {
private:
    enum TokType kind; // can't have a union here b/c string can't be in one 8-(
    unsigned short value; // kind == number only
    string name;    // kind == identifier only
public:
    Token(const TokType k) : kind(k) {}
    Token(const unsigned short val) : value(val) { kind = number; }
    Token(const string & moniker) : name(moniker) { kind = identifier; }
    enum TokType get_kind() const { return kind; }
    string get_name() const { return name; }
    unsigned short get_value() const { return value; }
};

bool is_number(const string & str) {
    return  str[0] >= '0' && str[0] <= '9';
}

Token str_to_tok(const string & str) {
    // This could be implemented various ways, including this quick 'n'
    // dirty and clunky way.  Trying to take them in order of expected
    // frequency, except for identifier
    if (str == "->")  {
        return Token(assign);
    }
    if (is_number(str)) {
        return Token(stoi(str));
    }
    if (str == "NOT") {
        return Token(nott);
    }
    if (str == "AND") {
        return Token(andd);
    }
    if (str == "OR") {
        return Token(orr);
    }
    if (str == "LSHIFT") {
        return Token(lshift);
    }
    if (str == "RSHIFT") {
        return Token(rshift);
    }
    return Token(str); // identifier
}

Token get_tok(string_tokeniser & splitter) {
    if (!splitter.next(' ')) return Token(end_of_line);
    string str;
    splitter.get_token(str);
    return str_to_tok(str);
}

// Expression/Statement nodes
// struct rather than class just to emphasize how non O-O this is 8-)

struct Node {
private:
    TokType kind;
    Node * left, *right;
    string name; // when kind == identifier
    unsigned short value; // when kind = number;

    Node * operand() { return left; }
public:
    enum TokType get_kind() { return kind; }
    string get_name() { return name; }
    void set_name(string str) { name = str; }
    unsigned short get_value() { return value; }
    void set_value(unsigned short val) { value = val; }

    /* may need for constand folding for convenience - could be private */
    /*
    Node * left_operand() { return left; }
    Node * right_operand() { return right; }

    void set_operand(Node * operand) {
    assert(kind == nott);
    left = operand;
    }
    void set_left_operand(Node * leftop) {
    assert(is_binary_op());
    left = leftop;
    }
    void set_right_operand(Node * rightop) {
    assert(is_binary_op());
    right = rightop;
    }
    */

    // can't make a generic Node with no operands and no name or
    // value, right?
    // Node(TokType theKind) : kind(theKind), left(NULL), right(NULL) {}
    // should these ctors have asserts on kind vs operand signature?
    Node(TokType theKind, string theName) : kind(theKind), name(theName) {}
    Node(TokType theKind, unsigned short theValue) : kind(theKind), value(theValue) {}
    Node(TokType theKind, Node * operand) : kind(theKind), left(operand), right(NULL)  {}
    Node(TokType theKind, Node * leftop, Node * rightop)
            : kind(theKind), left(leftop), right(rightop) {}

    bool fold();
};

/**************** Symbol Table ****************/

typedef unordered_map<string, Node *> SymbolTable;

SymbolTable symtable;

/*
    symbol table operations:

      insert(const value_type & elem) where elem is pair<const key_type, mapped_type>

      cf. make_pair library function
      pair <string, Node *> symtable_temp;
      symtable_temp = make_pair( some_string, some_name * );

      iterator find ( const key_type& k );
      returns unordered_multimap::end if not found

      walking the map (iterators)
      for ( auto it = symtable.begin(); it != symtable.end(); ++it )
          std::cout << " " << it->first << ":" << it->second;
*/

void make_symtable_entry(string sym_name, Node * val_expr) {
	symtable.insert(make_pair(sym_name, val_expr));
}

void print_symtable() {
    for (auto it = symtable.begin(); it != symtable.end(); ++it) {
        cout << it->first << ": ";
        if (it->second->get_kind() == number) {
            cout << it->second->get_value();
        }
        else {
            cout << "not folded";
        }
        cout << endl;
    }
}

unsigned short eval_circuit(const string & goal) {
    bool complete = true;
    do {
        for (auto it = symtable.begin(); it != symtable.end(); ++it) {
            it->second->fold();
            if (it->second->get_kind() != number) {
                complete = false;
            }
            else if (it->first == goal) {
                return it->second->get_value();
            }
        }
    } while (!complete);
    // if we fall out the bottom here, we didn't fold to get the goal's value.
    // If goal not found, dump the entire symtable so we can see what's up
    print_symtable();
    cerr << "goal unfoldable or not found" << endl;
}

Node * expr_lookup(const string & theName) {
    SymbolTable::const_iterator sym_entry = symtable.find(theName);
    if (sym_entry == symtable.end()) {
            throw("expr_lookup: " + theName + " not found");
    }
    return sym_entry->second;
}

// enum TokType { nott, assign, andd, orr, lshift, rshift, identifier, number, end_of_line };
// outer call is from eval_circuit for the value expression of a symtable entry
bool Node::fold() {
    switch (kind) {
    case number:
        return true;
    case identifier: {
        // Do we know the value of this identifier?
        Node * operand_id_expr = expr_lookup(get_name());
        if (operand_id_expr->kind != number) {
                return false;
        }
        kind = number;
        value = operand_id_expr->value;
        return true;
    }
    case nott:
        if (!operand()->fold()) {
            return false;
        }
        assert(operand()->kind == number);
        kind = number;
        value = ~operand()->value;
        return true;
    case andd: case orr: case lshift: case rshift:
        if (!(left->fold() && right->fold())) {
            return false;
        }
        assert(left->kind == number && right->kind == number);
        if (kind == andd) {
            value = left->value & right->value;
        }
        else if (kind == orr) {
            value = left->value | right->value;
        }
        else if (kind == lshift) {
            value = left->value << right->value;
        }
        else if (kind == rshift) {
            value = left->value >> right->value;
        }
        kind = number;
        return true;
    default:
        cerr << "unexpected Node->kind in Node::fold()" << endl;
        return false;
    }
}

/******************* Parser ******************/
// Input is assumed to be correct, so no error checking.
// This is line-oriented input, kinda like assembly code.  There is no
// nesting with a line.  The chart of what-can-follow-what has only one
// major branch, splitting unary ops (of which there is only NOT) from
// binary ops (AND, OR, LSHIFT, RSHIFT)
// In words: you can have
//      NOT identifier ASSIGN (->) identifier
//      identifier ASSIGN identifier
//      identifier binop identifier ASSIGN identifier
//
// Now to code up a clean parser 8-)

class Parse {
private:
// these private methods are parser "actions"
    Node * ident(const Token & tok);
    Node * numeric(const Token & tok);
    void assignment(const Token & tok, Node * rhs, string_tokeniser & splitter);
    Node * binop(const Token & tok, Node * lhs, string_tokeniser & splitter);
    Node * negation(const Token & tok, Node * operand);
    Node * negation(const Token & tok, string_tokeniser & splitter);
public:
    void parse(const string & line);
};

Node * Parse::numeric(const Token & tok) {
    assert(tok.get_kind() == number);
    Node * num_node = new Node(number, tok.get_value());
    return num_node;
}

Node * Parse::ident(const Token & tok) {
    assert(tok.get_kind() == identifier);
    string id_name = tok.get_name();
    Node * id_node = new Node(identifier, id_name);
    // NOOOO!!! Only enter when target of assignment
    // make_symtable_entry(id_name, id_node);
    return id_node;
}

// assignment differs from other binops in that the operand seen after
// the operator name goes on the left
void Parse::assignment(const Token & tok, Node * rhs, string_tokeniser & splitter) {
    assert(tok.get_kind() == assign);
    Token lhs_tok = get_tok(splitter);
    assert(lhs_tok.get_kind() == identifier);
    // Nope - we don't make assignment nodes.  Instead
    // an assignment becomes a pair in the symtable
    // Node * lhs = ident(lhs_tok);
    // Node * result = new Node(assign, lhs, rhs);
    make_symtable_entry(lhs_tok.get_name(), rhs);
    // return result; // no result to return ... at end of statement/line anyway
}

// AND, OR, LSHIFT, RSHIFT
Node * Parse::binop(const Token & tok, Node * lhs, string_tokeniser & splitter) {
    TokType theOp = tok.get_kind();
    assert(theOp == andd || theOp == orr ||
           theOp == lshift || theOp == rshift);
    Token rhs_tok = get_tok(splitter);
    TokType rhs_type = rhs_tok.get_kind();
    assert(rhs_type == identifier || rhs_type == number);
    Node * rhs = rhs_type == identifier
        ? ident(rhs_tok.get_name())
        : numeric(rhs_tok.get_value());
    Node * op_node = new Node(theOp, lhs, rhs);
    return op_node;
}

// TODO: all this looking ahead is the same as in binop - factor it out!
// Could Parse itself use it?

// the only unary op is NOT
Node * Parse::negation(const Token & tok, string_tokeniser & splitter) {
    assert(tok.get_kind() == nott);
    Token operand_tok = get_tok(splitter);
    TokType operand_type = operand_tok.get_kind();
    assert(operand_type == identifier || operand_type == number);
    Node * theOperand = operand_type == identifier
        ? ident(operand_tok.get_name())
        : numeric(operand_tok.get_value());
    Node * not_node = new Node(nott, theOperand);
    return not_node;
}

void Parse::parse(const string & line)
{
    // Want this static in the class so
    // we can init it only once, and we
    // don't have to pass it to every routine.
    class string_tokeniser splitter(line);

    Token cur_tok(end_of_line);
    cur_tok = get_tok(splitter);
    enum TokType tok_kind;
    Node * cur_node = NULL;

    // Invariant 1: finish loop with cur_node pointing to what current iteration created.
    // Invariant 2 (proposed): cur_tok is the next token to be processed.
    // Question: who should fetch the next token?  Do it here at
    // loop bottom, or have each parser action do it?  Prefer the
    // former.

    while ((tok_kind = cur_tok.get_kind()) != end_of_line) {
        switch (tok_kind) {
        case identifier:
            cur_node = ident(cur_tok);
            break;
        case number:
            cur_node = numeric(cur_tok);
            break;
        case assign:
            // note no cur_tok as we're done with line at this point
            assignment(cur_tok, cur_node, splitter);
            break;
        case andd: case orr: case lshift: case rshift:
            cur_node = binop(cur_tok, cur_node, splitter);
            break;
        case nott:
            cur_node = negation(cur_tok, splitter);
            break;
        default:
            assert(false);
            break;
        }
        cur_tok = get_tok(splitter);
    }
}

// int _tmain(int argc, _TCHAR* argv[])
int main(int argc, char *argv[])
{
    string goal = "a";
    if (argc != 2) {
        cout << "usage: " << argv[0] << "<filename>\n";
        return 1;
    }

    Parse parser;
    ifstream ifs(argv[1]);
    string line;

    while (getline(ifs, line)) {
            parser.parse(line);
    }

    // walk symtable and eval until goal is found folded

    unsigned short answer = eval_circuit(goal);
    cout << "The value of '" << goal << "' is " << answer << endl;

#ifdef PC
    cout << "\nClose window or click stop to exit ...";
    char foo[100];
    cin >> foo;
#endif

    return 0;
}

// EOF

