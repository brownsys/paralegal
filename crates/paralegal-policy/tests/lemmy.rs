mod helpers;

use helpers::{Result, Test};

#[test]
fn async_trait() -> Result<()> {
    let mut test = Test::new(stringify!(
        pub struct SaveComment {
            pub comment_id: CommentId,
            pub save: bool,
            pub auth: Sensitive<String>,
        }
        #[async_trait::async_trait(?Send)]
        pub trait Perform {
            type Response: serde::ser::Serialize + Send;

            async fn perform(
                &self,
                context: &Data<LemmyContext>,
            ) -> Result<Self::Response, LemmyError>;
        }

        #[async_trait::async_trait(?Send)]
        impl Perform for SaveComment {
            #[cfg_attr(feature = "comment-save", paralegal::analyze)]
            async fn perform(
                &self,
                context: &Data<LemmyContext>,
            ) -> Result<CommentResponse, LemmyError> {
                let data: &SaveComment = self;
                let local_user_view =
                    get_local_user_view_from_jwt(&data.auth, context.pool(), context.secret())
                        .await?;

                let comment_saved_form = CommentSavedForm {
                    comment_id: data.comment_id,
                    person_id: local_user_view.person.id,
                };

                if data.save {
                    let save_comment =
                        move |conn: &'_ _| CommentSaved::save(conn, &comment_saved_form);
                    apply_label_community_write(
                        blocking(context.pool(), save_comment).await?.map_err(|e| {
                            LemmyError::from_error_message(e, "couldnt_save_comment")
                        })?,
                    );
                } else {
                    let unsave_comment =
                        move |conn: &'_ _| CommentSaved::unsave(conn, &comment_saved_form);
                    apply_label_community_write(
                        blocking(context.pool(), unsave_comment)
                            .await?
                            .map_err(|e| {
                                LemmyError::from_error_message(e, "couldnt_save_comment")
                            })?,
                    );
                }

                let comment_id = data.comment_id;
                let person_id = local_user_view.person.id;
                let comment_view = apply_label_read(
                    blocking(context.pool(), move |conn| {
                        CommentView::read(conn, comment_id, Some(person_id))
                    })
                    .await??,
                );

                Ok(CommentResponse {
                    comment_view,
                    recipient_ids: Vec::new(),
                    form_id: None,
                })
            }
        }
    ))?;

    test.with_dep(["async-trait@0.1"]);

    test.run(|ctx| Ok(()))
}
