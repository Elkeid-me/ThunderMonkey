// Copyright (C) 2024 一梦全能 team
//
// This file is part of ThunderMonkey.
//
// ThunderMonkey is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// ThunderMonkey is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with ThunderMonkey.  If not, see <http://www.gnu.org/licenses/>.

use generator::{done, Gn};

pub fn preprocess(code: String) -> String {
    let remove_cr = Gn::new_scoped(move |mut s| {
        enum RmCrState {
            Normal,
            Cr,
        }
        use RmCrState::*;
        let mut state = Normal;
        for c in code.chars() {
            match (&state, c) {
                (Normal, '\r') => state = Cr,
                (Normal, _) => {
                    s.yield_(c);
                }
                (Cr, '\n') => {
                    state = Normal;
                    s.yield_('\n');
                }
                (Cr, '\r') => {
                    s.yield_('\n');
                }
                (Cr, _) => {
                    state = Normal;
                    s.yield_('\n');
                    s.yield_(c);
                }
            }
        }
        if let Cr = state {
            s.yield_('\r');
        }
        done!();
    });
    let phy_line_to_logical_line = Gn::new_scoped(move |mut s| {
        enum P2LState {
            Normal,
            Backslash,
        }
        use P2LState::*;
        let mut state = Normal;
        for c in remove_cr {
            match (&state, c) {
                (Normal, '\\') => state = Backslash,
                (Normal, _) => {
                    s.yield_(c);
                }
                (Backslash, '\n') => state = Normal,
                (Backslash, '\\') => {
                    s.yield_('\\');
                }
                (Backslash, _) => {
                    state = Normal;
                    s.yield_('\\');
                    s.yield_(c);
                }
            }
        }
        if let Backslash = state {
            s.yield_('\\');
        }
        done!()
    });
    let remove_comments = Gn::new_scoped(move |mut s| {
        enum State {
            Code,
            CodeWithSlash,
            StringLiteral,
            StringLiteralWithEscape,
            Comment,
            CxxComment,
            CommentWithStar,
        }
        use State::*;
        let mut state = Code;
        for c in phy_line_to_logical_line {
            match (&state, c) {
                (Code, '/') => state = CodeWithSlash,
                (Code, '"') => {
                    state = StringLiteral;
                    s.yield_('"');
                }
                (Code, _) => {
                    s.yield_(c);
                }
                (CodeWithSlash, '/') => state = CxxComment,
                (CodeWithSlash, '*') => state = Comment,
                (CodeWithSlash, _) => {
                    state = Code;
                    s.yield_('/');
                    s.yield_(c);
                }
                (StringLiteral, '\\') => state = StringLiteralWithEscape,
                (StringLiteral, '"') => {
                    state = Code;
                    s.yield_('"');
                }
                (StringLiteral, _) => {
                    s.yield_(c);
                }
                (StringLiteralWithEscape, _) => {
                    state = StringLiteral;
                    s.yield_('\\');
                    s.yield_(c);
                }
                (Comment, '*') => state = CommentWithStar,
                (Comment, _) => (),
                (CommentWithStar, '/') => {
                    state = Code;
                    s.yield_(' ');
                }
                (CommentWithStar, '*') => (),
                (CommentWithStar, _) => state = Comment,
                (CxxComment, '\n') => {
                    state = Code;
                    s.yield_('\n');
                }
                (CxxComment, _) => (),
            }
        }
        done!()
    });
    remove_comments.into_iter().collect()
}
